// Public staged trees use sealed lifecycle and level traits internally.
#![allow(private_bounds)]

use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use super::{PTPage, PTPageMutRef, PTPageRef, WalkLevelImpl};
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::{KernelPolicy, OwnedIndices, PagingOwnershipPolicy};
use crate::structs::sizes::{entry_index, PageSize, PT_ENTRY_COUNT};
use crate::structs::sizes::{Huge, Regular};
use crate::structs::tlb::FlushedBatch;

/// A private tree that owns every attached descendant.
pub struct Staged;

/// An unlinked tree awaiting hardware page-walk synchronization.
pub(crate) struct Detached;

/// An unlinked page-table subtree retained until page-walk synchronization.
#[must_use = "a detached page-table subtree must be reclaimed after synchronization or retained"]
pub struct DetachedPageTable<'id, A: ArchPagingMeta, P: PagingAllocator> {
    inner: DetachedPageTableInner<A, P>,
    marker: PhantomData<&'id mut &'id mut ()>,
}

/// A synchronized detached subtree that reclaims its tables on drop.
pub struct StagedPageTable<A: ArchPagingMeta, P: PagingAllocator> {
    inner: Option<StagedPageTableInner<A, P>>,
}

enum DetachedPageTableInner<A: ArchPagingMeta, P: PagingAllocator> {
    L0(PTPageTree<A, P, Lvl<0>, KernelPolicy, Detached>),
    L1(PTPageTree<A, P, Lvl<1>, KernelPolicy, Detached>),
    L2(PTPageTree<A, P, Lvl<2>, KernelPolicy, Detached>),
    L3(PTPageTree<A, P, Lvl<3>, KernelPolicy, Detached>),
    L4(PTPageTree<A, P, Lvl<4>, KernelPolicy, Detached>),
}

enum StagedPageTableInner<A: ArchPagingMeta, P: PagingAllocator> {
    L0(PTPageTree<A, P, Lvl<0>, KernelPolicy, Staged>),
    L1(PTPageTree<A, P, Lvl<1>, KernelPolicy, Staged>),
    L2(PTPageTree<A, P, Lvl<2>, KernelPolicy, Staged>),
    L3(PTPageTree<A, P, Lvl<3>, KernelPolicy, Staged>),
    L4(PTPageTree<A, P, Lvl<4>, KernelPolicy, Staged>),
}

/// A tree whose entries may be observed through live atomic views.
pub(crate) struct Live;

pub(crate) trait SplitLeafChange<A: ArchPagingMeta>: Copy {
    fn apply(self, entry: PTEntry<A>) -> PTEntry<A>;
}

#[derive(Clone, Copy)]
pub(crate) struct PreserveSplitLeaf;

impl<A: ArchPagingMeta> SplitLeafChange<A> for PreserveSplitLeaf {
    #[inline(always)]
    fn apply(self, entry: PTEntry<A>) -> PTEntry<A> {
        entry
    }
}

#[derive(Clone, Copy)]
pub(crate) struct SplitLeafFlags<A: ArchPagingMeta>(pub A::PTFlags);

impl<A: ArchPagingMeta> SplitLeafChange<A> for SplitLeafFlags<A> {
    #[inline(always)]
    fn apply(self, mut entry: PTEntry<A>) -> PTEntry<A> {
        let mask = A::leaf_flags_mask();
        entry.clear_flags(mask);
        entry.set_flags(self.0 & mask);
        entry
    }
}

#[derive(Clone, Copy)]
pub(crate) struct SplitLeafEncryption(pub bool);

impl<A: ArchPagingMeta> SplitLeafChange<A> for SplitLeafEncryption {
    #[inline(always)]
    fn apply(self, mut entry: PTEntry<A>) -> PTEntry<A> {
        if self.0 {
            entry.make_shared();
        } else {
            entry.make_private();
        }
        entry
    }
}

/// Selects descendant ownership from the tree lifecycle.
pub(crate) trait TreeState {
    const RECLAIM_ON_DROP: bool;

    /// Returns whether the tree owns the subtree at this root index.
    fn owns_top_entry<S: PagingOwnershipPolicy>(index: usize) -> bool;
}

pub(crate) trait AccessibleTreeState: TreeState {}

type DetachedChildTree<A, P, L> =
    PTPageTree<A, P, <L as WalkLevelImpl>::ChildLevel, KernelPolicy, Detached>;

/// Builds deeper staged split trees through statically selected child levels.
pub(crate) trait StagedSplitLevel: InnerLevel + WalkLevelImpl
where
    Self::Child: WalkLevelImpl,
{
    fn attach_split<A, P, PS, C, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
        S: PagingOwnershipPolicy + Clone;
}

impl StagedSplitLevel for Lvl<1> {
    fn attach_split<A, P, PS, C, S>(
        _: PTEntry<A>,
        _: Page<PS>,
        _: C,
        _: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
        S: PagingOwnershipPolicy + Clone,
    {
        Err(PagingError::InvalidLevel)
    }
}

fn attach_split_tree<A, P, L, PS, C, S>(
    entry: PTEntry<A>,
    target_page: Page<PS>,
    change: C,
    policy: S,
) -> Result<PTEntry<A>, PagingError>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: StagedSplitLevel,
    L::Child: WalkLevelImpl,
    PS: PageSize,
    C: SplitLeafChange<A>,
    S: PagingOwnershipPolicy + Clone,
{
    let subtree = PTPageTree::<A, P, L, S>::new_split(entry, target_page, change, policy)?;
    let child = PTEntry::new_table(
        A::make_private_address(subtree.root_paddr()),
        A::PTFlags::parent_flags(),
    );
    subtree.release();
    Ok(child)
}

impl StagedSplitLevel for Lvl<2> {
    fn attach_split<A, P, PS, C, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_split_tree::<A, P, Lvl<1>, PS, C, S>(entry, target_page, change, policy)
    }
}

impl StagedSplitLevel for Lvl<3> {
    fn attach_split<A, P, PS, C, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_split_tree::<A, P, Lvl<2>, PS, C, S>(entry, target_page, change, policy)
    }
}

impl StagedSplitLevel for Lvl<4> {
    fn attach_split<A, P, PS, C, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_split_tree::<A, P, Lvl<3>, PS, C, S>(entry, target_page, change, policy)
    }
}

impl TreeState for Staged {
    const RECLAIM_ON_DROP: bool = true;

    fn owns_top_entry<S: PagingOwnershipPolicy>(_: usize) -> bool {
        true
    }
}

impl AccessibleTreeState for Staged {}

impl TreeState for Detached {
    const RECLAIM_ON_DROP: bool = false;

    fn owns_top_entry<S: PagingOwnershipPolicy>(_: usize) -> bool {
        true
    }
}

impl TreeState for Live {
    const RECLAIM_ON_DROP: bool = true;

    fn owns_top_entry<S: PagingOwnershipPolicy>(index: usize) -> bool {
        <S::Owned as OwnedIndices>::contains(index)
    }
}

impl AccessibleTreeState for Live {}

/// Owns its root and descendant tables, never mapped data frames.
/// Staged trees own every descendant; live trees defer root ownership to policy.
#[allow(private_bounds)]
pub struct PTPageTree<
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevelImpl,
    S: PagingOwnershipPolicy = KernelPolicy,
    State: TreeState = Staged,
> {
    root: PhysAddr,
    policy: S,
    marker: PhantomData<(A, P, L, State)>,
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S, Staged>
{
    /// Allocates an empty staged root with a static level.
    pub(crate) fn new_root(policy: S) -> Result<Self, PagingError> {
        let (_, root) = PTPage::<A, P>::alloc()?;
        Ok(Self { root, policy, marker: PhantomData })
    }

    /// Enables live atomic access while preserving the tree's ownership policy.
    pub(crate) fn into_live(self) -> PTPageTree<A, P, L, S, Live> {
        let (policy, root) = self.into_parts();
        PTPageTree { root, policy, marker: PhantomData }
    }

    /// Returns ordinary mutable storage for this unpublished root page.
    pub(crate) fn root_page_mut(&mut self) -> &mut PTPage<A, P> {
        let vaddr = P::paddr_to_vaddr(self.root);
        // SAFETY: staged-tree ownership keeps the root unpublished and exclusive.
        unsafe { &mut *vaddr.as_mut_ptr() }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>
    PTPageTree<A, P, L, KernelPolicy, Staged>
{
    /// Imports an unlinked owned subtree.
    ///
    /// # Safety
    /// `root` must be an initialized, correctly leveled, acyclic tree allocated
    /// by `P`. Every table page must be exclusively owned, mapped, writable,
    /// and have no other parent or hardware users.
    pub unsafe fn from_owned_root(root: PhysAddr) -> Self {
        Self { root, policy: KernelPolicy::new(), marker: PhantomData }
    }

    /// # Safety
    /// `root` must be a currently live allocation owned by `P`, and its
    /// exclusive ownership must be transferred to the returned tree. Drop
    /// always frees the root, so the caller must neither retain ownership nor
    /// deallocate it. The root must be initialized at `L::LEVEL`, with an
    /// acyclic, correctly leveled tree whose pages stay mapped, writable and
    /// pinned for this owner.
    /// Every descendant table must be allocator-allocated and exclusively owned,
    /// without other parent links. Suppress Drop unless all users are quiesced.
    pub unsafe fn from_root(root: PhysAddr) -> Result<Self, PagingError> {
        // SAFETY: the caller supplies the ownership and structural requirements.
        let tree = ManuallyDrop::new(unsafe { Self::from_owned_root(root) });
        tree.validate()?;
        Ok(ManuallyDrop::into_inner(tree))
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>
    PTPageTree<A, P, L, KernelPolicy, Detached>
{
    /// Makes the detached tree privately mutable and reclaimable.
    ///
    /// # Safety
    /// All hardware page walks that could have observed the old parent link must
    /// have completed, and every cached paging-structure reference must have
    /// been invalidated. The subtree must be uniquely owned and allocated by `P`.
    pub(crate) unsafe fn into_staged_after_flush(
        self,
    ) -> PTPageTree<A, P, L, KernelPolicy, Staged> {
        let (policy, root) = self.into_parts();
        PTPageTree { root, policy, marker: PhantomData }
    }

    /// Erases the static root level so detached trees can be gathered together.
    pub(super) fn erase<'id>(self) -> DetachedPageTable<'id, A, P> {
        L::erase_detached(self)
    }
}

impl<'id, A: ArchPagingMeta, P: PagingAllocator> DetachedPageTable<'id, A, P> {
    pub(super) fn from_l0(tree: PTPageTree<A, P, Lvl<0>, KernelPolicy, Detached>) -> Self {
        Self { inner: DetachedPageTableInner::L0(tree), marker: PhantomData }
    }

    pub(super) fn from_l1(tree: PTPageTree<A, P, Lvl<1>, KernelPolicy, Detached>) -> Self {
        Self { inner: DetachedPageTableInner::L1(tree), marker: PhantomData }
    }

    pub(super) fn from_l2(tree: PTPageTree<A, P, Lvl<2>, KernelPolicy, Detached>) -> Self {
        Self { inner: DetachedPageTableInner::L2(tree), marker: PhantomData }
    }

    pub(super) fn from_l3(tree: PTPageTree<A, P, Lvl<3>, KernelPolicy, Detached>) -> Self {
        Self { inner: DetachedPageTableInner::L3(tree), marker: PhantomData }
    }

    pub(super) fn from_l4(tree: PTPageTree<A, P, Lvl<4>, KernelPolicy, Detached>) -> Self {
        Self { inner: DetachedPageTableInner::L4(tree), marker: PhantomData }
    }

    /// Makes this subtree reclaimable after parent-link invalidation completes.
    ///
    /// # Safety
    /// Every hardware walk that could have observed the removed parent link
    /// must have completed, and every corresponding paging-structure cache
    /// entry must have been invalidated. The subtree must remain uniquely owned.
    pub fn into_staged_after_flush(self, _: &FlushedBatch<'id>) -> StagedPageTable<A, P> {
        // SAFETY: the matching batch proof establishes hardware exclusion.
        unsafe { self.into_staged_after_flush_unchecked() }
    }

    pub(crate) unsafe fn into_staged_after_flush_unchecked(self) -> StagedPageTable<A, P> {
        let inner = match self.inner {
            DetachedPageTableInner::L0(tree) => {
                StagedPageTableInner::L0(unsafe { tree.into_staged_after_flush() })
            }
            DetachedPageTableInner::L1(tree) => {
                StagedPageTableInner::L1(unsafe { tree.into_staged_after_flush() })
            }
            DetachedPageTableInner::L2(tree) => {
                StagedPageTableInner::L2(unsafe { tree.into_staged_after_flush() })
            }
            DetachedPageTableInner::L3(tree) => {
                StagedPageTableInner::L3(unsafe { tree.into_staged_after_flush() })
            }
            DetachedPageTableInner::L4(tree) => {
                StagedPageTableInner::L4(unsafe { tree.into_staged_after_flush() })
            }
        };
        StagedPageTable { inner: Some(inner) }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> Drop for StagedPageTable<A, P> {
    fn drop(&mut self) {
        match self.inner.take().expect("staged subtree is dropped once") {
            StagedPageTableInner::L0(tree) => drop(tree),
            StagedPageTableInner::L1(tree) => drop(tree),
            StagedPageTableInner::L2(tree) => drop(tree),
            StagedPageTableInner::L3(tree) => drop(tree),
            StagedPageTableInner::L4(tree) => drop(tree),
        }
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> PTPageMutRef<'tree, A, P, L> {
    /// Unlinks one child table and returns ownership without reclaiming it.
    pub(crate) fn detach_subtree(
        &mut self,
        index: usize,
    ) -> Result<DetachedChildTree<A, P, L>, PTEntry<A>> {
        let entry = self.load(index);
        if !entry.is_present_table(self.level()) {
            return Err(entry);
        }
        let detached = self.swap(index, PTEntry::empty());
        debug_assert!(detached.is_present_table(self.level()));
        Ok(PTPageTree {
            root: PhysAddr::from(detached.address()),
            policy: KernelPolicy::new(),
            marker: PhantomData,
        })
    }
}

impl<A: ArchPagingMeta, P: DirectMappedAllocator, L: WalkLevelImpl>
    PTPageTree<A, P, L, KernelPolicy, Staged>
{
    /// Builds a staged tree that maps the allocator's direct map.
    pub(crate) fn new_direct_mapped(flags: A::PTFlags) -> Result<Self, PagingError> {
        let (phys, _) = P::direct_map();
        let start = P::paddr_to_vaddr(phys.start);
        let end = P::paddr_to_vaddr(phys.end);
        let small = PageLevel::Level0;
        let large = PageLevel::Level1;
        assert!(start <= end && start.is_aligned(small.size()) && end.is_aligned(small.size()));
        assert!(phys.start.is_aligned(small.size()));
        let mut tree = PTPageTree::<A, P, L, KernelPolicy, Staged>::new_root(KernelPolicy::new())?;
        {
            let page = tree.root_page_mut();
            let parent_flags = A::PTFlags::parent_flags();
            let mut vaddr = start;
            while vaddr < end {
                let paddr = phys.start + (vaddr - start);
                let target = if L::LEVEL >= large
                    && vaddr.is_aligned(large.size())
                    && paddr.is_aligned(large.size())
                    && end - vaddr >= large.size()
                {
                    large
                } else {
                    small
                };
                // SAFETY: all pages remain exclusively owned by this tree.
                match target {
                    PageLevel::Level0 => unsafe {
                        PTPage::map_unpublished(
                            page,
                            L::LEVEL,
                            Page::<Regular>::from_start_address(vaddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            PhysFrame::<Regular>::from_start_address(paddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            flags,
                            false,
                            parent_flags,
                        )
                    },
                    PageLevel::Level1 => unsafe {
                        PTPage::map_unpublished(
                            page,
                            L::LEVEL,
                            Page::<Huge>::from_start_address(vaddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            PhysFrame::<Huge>::from_start_address(paddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            flags,
                            false,
                            parent_flags,
                        )
                    },
                    _ => Err(PagingError::InvalidLevel),
                }?;
                vaddr = vaddr + target.size();
            }
        }
        Ok(tree)
    }
}

impl<A, P, L, S> PTPageTree<A, P, L, S, Staged>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: StagedSplitLevel,
    L::Child: WalkLevelImpl,
    S: PagingOwnershipPolicy,
{
    /// Builds a staged replacement tree for one split leaf.
    pub(super) fn new_split<PS: PageSize, C: SplitLeafChange<A>>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
        policy: S,
    ) -> Result<PTPageTree<A, P, L::Child, S, Staged>, PagingError>
    where
        S: Clone,
    {
        let target = PS::LEVEL;
        let vaddr = target_page.start_address();
        let child_level = L::Child::LEVEL;
        let mut tree = PTPageTree::<A, P, L::Child, S, Staged>::new_root(policy.clone())?;
        let page = tree.root_page_mut();
        let target_index = entry_index(vaddr, child_level);
        for idx in 0..PT_ENTRY_COUNT {
            let mut child = entry.split_child(L::LEVEL, idx);
            if idx != target_index {
                *page.entry_mut(idx) = child;
                continue;
            }
            if child_level > target {
                child =
                    L::attach_split::<A, P, PS, C, S>(child, target_page, change, policy.clone())?;
            } else {
                child = change.apply(child);
            }
            *page.entry_mut(idx) = child;
        }
        Ok(tree)
    }
}

impl<
        A: ArchPagingMeta,
        P: PagingAllocator,
        L: WalkLevelImpl,
        S: PagingOwnershipPolicy,
        State: TreeState,
    > PTPageTree<A, P, L, S, State>
{
    pub(crate) fn into_parts(self) -> (S, PhysAddr) {
        let root = self.root;
        let policy = unsafe { core::ptr::read(&self.policy) };
        core::mem::forget(self);
        (policy, root)
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S, Staged>
{
    /// Transfers ownership of the whole subtree without freeing it.
    /// The recipient must retain a compatible allocator for the released pages.
    pub(crate) fn release(self) -> PhysAddr {
        let (_, root) = self.into_parts();
        root
    }
}

impl<
        A: ArchPagingMeta,
        P: PagingAllocator,
        L: WalkLevelImpl,
        S: PagingOwnershipPolicy,
        State: TreeState,
    > Drop for PTPageTree<A, P, L, S, State>
{
    /// Inputs: owned tree.
    /// Requires: quiesced owned pages.
    /// Returns: nothing.
    fn drop(&mut self) {
        if !State::RECLAIM_ON_DROP {
            return;
        }
        // SAFETY: owned tables are quiesced before Drop; shared subtrees are excluded.
        // SAFETY: reclaimable tree states require quiescence before Drop.
        let mut root: PTPageMutRef<'_, A, P, L> = unsafe { PTPageMutRef::from_root(self.root) };
        unsafe { root.free_children(State::owns_top_entry::<S>) };
        // SAFETY: descendant references have ended and this root is exclusively owned.
        unsafe { P::deallocate_table_page(self.root) };
    }
}

impl<
        A: ArchPagingMeta,
        P: PagingAllocator,
        L: WalkLevelImpl,
        S: PagingOwnershipPolicy,
        State: AccessibleTreeState,
    > PTPageTree<A, P, L, S, State>
{
    pub(crate) fn validate(&self) -> Result<(), PagingError> {
        self.validate_page::<L>(self.root)
    }

    /// Inputs: current typed table.
    /// Requires: accessible stable tree.
    /// Returns: validation status.
    fn validate_page<PL: WalkLevelImpl>(&self, paddr: PhysAddr) -> Result<(), PagingError> {
        let vaddr = P::paddr_to_vaddr(paddr);
        self.validate_self_mapping(paddr, vaddr)?;
        if PL::LEVEL == PageLevel::Level0 {
            return Ok(());
        }
        // SAFETY: validation starts from an owner-pinned page at the static level `PL`.
        let page = unsafe { PTPageRef::<A, P, PL>::from_root(paddr) };
        for idx in 0..PT_ENTRY_COUNT {
            let entry = page.load(idx);
            if !entry.is_present_table(PL::LEVEL) {
                continue;
            }
            self.validate_page::<PL::ChildLevel>(PhysAddr::from(entry.address()))?;
        }
        Ok(())
    }

    /// Inputs: table addresses.
    /// Requires: stable tree.
    /// Returns: self-mapping status.
    fn validate_self_mapping(&self, paddr: PhysAddr, vaddr: VirtAddr) -> Result<(), PagingError> {
        let mapping = self.root().walk(vaddr);
        let level = mapping.level();
        let entry = mapping.read();
        let translated =
            (entry.address() & !(level.size() - 1)) + (vaddr.bits() & (level.size() - 1));
        if !entry.is_present_leaf(level) || translated != paddr.bits() {
            return Err(PagingError::TablePageNotSelfMapped);
        }
        Ok(())
    }
}

impl<
        A: ArchPagingMeta,
        P: PagingAllocator,
        L: WalkLevelImpl,
        S: PagingOwnershipPolicy,
        State: AccessibleTreeState,
    > PTPageTree<A, P, L, S, State>
{
    pub fn root_paddr(&self) -> PhysAddr {
        self.root
    }

    pub(crate) fn policy(&self) -> &S {
        &self.policy
    }

    pub(crate) fn root(&self) -> PTPageRef<'_, A, P, L> {
        // SAFETY: the owner borrow pins the initialized tree and its reachable tables.
        unsafe { PTPageRef::from_root(self.root) }
    }

    /// Returns tree-exclusive atomic access to the root topology.
    pub(crate) fn root_mut(&mut self) -> PTPageMutRef<'_, A, P, L> {
        // SAFETY: the mutable tree borrow excludes every software tree accessor.
        unsafe { PTPageMutRef::from_root(self.root) }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl, S: PagingOwnershipPolicy>
    PTPageTree<A, P, L, S, Staged>
{
    /// Adds missing tables down to `target`, without splitting existing leaves.
    pub(crate) fn grow<PS: PageSize>(
        &mut self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
        if target > L::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        self.root_mut().grow_uninstalled(target_page, parent_flags)
    }

    /// Stores one leaf in this unpublished, already-grown tree.
    pub(crate) fn store_uninstalled<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        entry: PTEntry<A>,
    ) -> Result<(), PagingError> {
        self.root_mut().store_uninstalled(page, entry)
    }
}
