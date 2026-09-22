use core::marker::PhantomData;
use core::mem::ManuallyDrop;

use super::{PTPage, PTPagePointer, PageLevelVisitor, WalkLevelImpl};
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy};
use crate::structs::sizes::{entry_index, PageSize, PT_ENTRY_COUNT};
use crate::structs::sizes::{Huge, Regular};

/// A private tree that owns every attached descendant.
pub(crate) struct Staged;

/// A tree whose entries may be observed through live atomic views.
pub(crate) struct Live;

/// Selects descendant ownership from the tree lifecycle.
pub(crate) trait TreeState {
    /// Returns whether the tree owns the subtree at this root index.
    fn owns_top_entry<S: PagingOwnershipPolicy>(policy: &S, index: usize) -> bool;
}

/// Builds deeper staged split trees through statically selected child levels.
pub(crate) trait StagedSplitLevel: InnerLevel + WalkLevelImpl
where
    Self::Child: WalkLevelImpl,
{
    fn attach_split<A, P, PS, F, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
        S: PagingOwnershipPolicy + Clone;

    fn attach_range_split<A, P, S>(
        entry: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        S: PagingOwnershipPolicy + Clone;
}

impl StagedSplitLevel for Lvl<1> {
    fn attach_split<A, P, PS, F, S>(
        _: PTEntry<A>,
        _: Page<PS>,
        _: F,
        _: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
        S: PagingOwnershipPolicy + Clone,
    {
        Err(PagingError::InvalidLevel)
    }

    fn attach_range_split<A, P, S>(
        _: PTEntry<A>,
        _: usize,
        _: usize,
        _: A::PTFlags,
        _: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        S: PagingOwnershipPolicy + Clone,
    {
        Err(PagingError::InvalidLevel)
    }
}

fn attach_split_tree<A, P, L, PS, F, S>(
    entry: PTEntry<A>,
    target_page: Page<PS>,
    update: F,
    policy: S,
) -> Result<PTEntry<A>, PagingError>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: StagedSplitLevel,
    L::Child: WalkLevelImpl,
    PS: PageSize,
    F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    S: PagingOwnershipPolicy + Clone,
{
    let subtree = PTPageTree::<A, P, L, S>::new_split(entry, target_page, update, policy)?;
    let child = PTEntry::new_table(
        A::make_private_address(subtree.root_paddr()),
        A::PTFlags::parent_flags(),
    );
    subtree.release();
    Ok(child)
}

fn attach_range_split_tree<A, P, L, S>(
    entry: PTEntry<A>,
    from: usize,
    to: usize,
    flags: A::PTFlags,
    policy: S,
) -> Result<PTEntry<A>, PagingError>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: StagedSplitLevel,
    L::Child: WalkLevelImpl,
    S: PagingOwnershipPolicy + Clone,
{
    let subtree = PTPageTree::<A, P, L, S>::new_range_split(entry, from, to, flags, policy)?;
    let child = PTEntry::new_table(
        A::make_private_address(subtree.root_paddr()),
        A::PTFlags::parent_flags(),
    );
    subtree.release();
    Ok(child)
}

impl StagedSplitLevel for Lvl<2> {
    fn attach_split<A, P, PS, F, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_split_tree::<A, P, Lvl<1>, PS, F, S>(entry, target_page, update, policy)
    }

    fn attach_range_split<A, P, S>(
        entry: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_range_split_tree::<A, P, Lvl<1>, S>(entry, from, to, flags, policy)
    }
}

impl StagedSplitLevel for Lvl<3> {
    fn attach_split<A, P, PS, F, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_split_tree::<A, P, Lvl<2>, PS, F, S>(entry, target_page, update, policy)
    }

    fn attach_range_split<A, P, S>(
        entry: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_range_split_tree::<A, P, Lvl<2>, S>(entry, from, to, flags, policy)
    }
}

impl StagedSplitLevel for Lvl<4> {
    fn attach_split<A, P, PS, F, S>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_split_tree::<A, P, Lvl<3>, PS, F, S>(entry, target_page, update, policy)
    }

    fn attach_range_split<A, P, S>(
        entry: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
        policy: S,
    ) -> Result<PTEntry<A>, PagingError>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        S: PagingOwnershipPolicy + Clone,
    {
        attach_range_split_tree::<A, P, Lvl<3>, S>(entry, from, to, flags, policy)
    }
}

impl TreeState for Staged {
    fn owns_top_entry<S: PagingOwnershipPolicy>(_: &S, _: usize) -> bool {
        true
    }
}

impl TreeState for Live {
    fn owns_top_entry<S: PagingOwnershipPolicy>(policy: &S, index: usize) -> bool {
        policy.owns_top_entry(index)
    }
}

/// Owns its root and descendant tables, never mapped data frames.
/// Staged trees own every descendant; live trees defer root ownership to policy.
pub(crate) struct PTPageTree<
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

struct ValidateChildrenVisitor<'a, A, P, L, S, State>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevelImpl,
    S: PagingOwnershipPolicy,
    State: TreeState,
{
    tree: &'a PTPageTree<A, P, L, S, State>,
}

impl<'tree, A, P, L, S, State> PageLevelVisitor<'tree, A, P>
    for ValidateChildrenVisitor<'_, A, P, L, S, State>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevelImpl,
    S: PagingOwnershipPolicy,
    State: TreeState,
{
    type Output = Result<(), PagingError>;

    fn visit_l0(self, _: PTPagePointer<'tree, A, P, Lvl<0>>) -> Self::Output {
        Ok(())
    }

    fn visit_l1(self, page: PTPagePointer<'tree, A, P, Lvl<1>>) -> Self::Output {
        self.tree.validate_child_tables(page)
    }

    fn visit_l2(self, page: PTPagePointer<'tree, A, P, Lvl<2>>) -> Self::Output {
        self.tree.validate_child_tables(page)
    }

    fn visit_l3(self, page: PTPagePointer<'tree, A, P, Lvl<3>>) -> Self::Output {
        self.tree.validate_child_tables(page)
    }

    fn visit_l4(self, page: PTPagePointer<'tree, A, P, Lvl<4>>) -> Self::Output {
        self.tree.validate_child_tables(page)
    }
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
}

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>
    PTPageTree<A, P, L, KernelPolicy, Staged>
{
    /// # Safety
    /// `root` must be a currently live allocation owned by `P`, and its
    /// exclusive ownership must be transferred to the returned tree. Drop
    /// always frees the root, so the caller must neither retain ownership nor
    /// deallocate it. The root must be initialized at `L::LEVEL`, with an
    /// acyclic, correctly leveled tree whose pages stay mapped, writable and
    /// pinned for this owner.
    /// Every descendant table must be allocator-allocated and exclusively owned,
    /// without other parent links. Suppress Drop unless all users are quiesced.
    pub(crate) unsafe fn from_root(root: PhysAddr) -> Result<Self, PagingError> {
        let tree = ManuallyDrop::new(Self { root, policy: KernelPolicy, marker: PhantomData });
        tree.validate()?;
        Ok(ManuallyDrop::into_inner(tree))
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
        let tree = PTPageTree::<A, P, L, KernelPolicy, Staged>::new_root(KernelPolicy)?;
        {
            let mut root = tree.root();
            // SAFETY: the new tree is exclusively owned and unpublished.
            let page = unsafe { root.page_mut() };
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

impl<
        A: ArchPagingMeta,
        P: PagingAllocator,
        L: InnerLevel + WalkLevelImpl,
        S: PagingOwnershipPolicy,
    > PTPageTree<A, P, L, S, Staged>
where
    L::Child: WalkLevelImpl,
{
    /// Builds one child table containing the finer leaves of `entry`.
    pub(super) fn new_leaf_split(
        entry: PTEntry<A>,
        policy: S,
    ) -> Result<PTPageTree<A, P, L::Child, S, Staged>, PagingError> {
        let tree = PTPageTree::<A, P, L::Child, S, Staged>::new_root(policy)?;
        let mut root = tree.root();
        // SAFETY: this tree is newly allocated and remains wholly uninstalled.
        unsafe { root.page_mut().refresh_leaf_split::<L>(entry) };
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
    pub(super) fn new_split<PS: PageSize, F>(
        entry: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
        policy: S,
    ) -> Result<PTPageTree<A, P, L::Child, S, Staged>, PagingError>
    where
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
        S: Clone,
    {
        let target = PS::LEVEL;
        let vaddr = target_page.start_address();
        let child_level = L::Child::LEVEL;
        let tree = PTPageTree::<A, P, L::Child, S, Staged>::new_root(policy.clone())?;
        let mut root = tree.root();
        // SAFETY: this tree is newly allocated and remains wholly uninstalled.
        let page = unsafe { root.page_mut() };
        let target_index = entry_index(vaddr, child_level);
        for idx in 0..PT_ENTRY_COUNT {
            let mut child = entry.split_child(L::LEVEL, idx);
            if idx != target_index {
                *page.entry_mut(idx) = child;
                continue;
            }
            if child_level > target {
                child =
                    L::attach_split::<A, P, PS, F, S>(child, target_page, update, policy.clone())?;
            } else {
                child = update(child, child_level);
            }
            *page.entry_mut(idx) = child;
        }
        Ok(tree)
    }

    /// Builds a staged replacement tree for a partially covered leaf range.
    pub(super) fn new_range_split(
        entry: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
        policy: S,
    ) -> Result<PTPageTree<A, P, L::Child, S, Staged>, PagingError>
    where
        S: Clone,
    {
        let child_level = L::Child::LEVEL;
        let tree = PTPageTree::<A, P, L::Child, S, Staged>::new_root(policy.clone())?;
        let mut root = tree.root();
        // SAFETY: this tree retains every initialized, uninstalled table page.
        let page = unsafe { root.page_mut() };
        for idx in 0..PT_ENTRY_COUNT {
            let mut child = entry.split_child(L::LEVEL, idx);
            let offset = idx * child_level.size();
            let first = from.saturating_sub(offset).min(child_level.size());
            let last = to.saturating_sub(offset).min(child_level.size());
            if first < last && !child_level.is_leaf() && (first != 0 || last != child_level.size())
            {
                child =
                    L::attach_range_split::<A, P, S>(child, first, last, flags, policy.clone())?;
            } else if first < last {
                PTPage::<A, P>::set_leaf_flags(&mut child, flags);
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
        // SAFETY: owned tables are quiesced before Drop; shared subtrees are excluded.
        unsafe { self.root().free_children(|index| State::owns_top_entry(&self.policy, index)) };
        // SAFETY: descendant references have ended and this root is exclusively owned.
        unsafe { P::deallocate_table_page(self.root) };
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
    pub(crate) fn validate(&self) -> Result<(), PagingError> {
        self.validate_page::<L>(self.root)
    }

    /// Inputs: current typed table.
    /// Requires: accessible stable tree.
    /// Returns: validation status.
    fn validate_page<PL: WalkLevelImpl>(&self, paddr: PhysAddr) -> Result<(), PagingError> {
        let vaddr = P::paddr_to_vaddr(paddr);
        self.validate_self_mapping(paddr, vaddr)?;
        // SAFETY: validation starts from an owner-pinned page at the static level `PL`.
        let page = unsafe { PTPagePointer::<A, P, PL>::from_root(paddr) };
        PL::dispatch(page, ValidateChildrenVisitor { tree: self })
    }

    /// Inputs: table addresses.
    /// Requires: stable tree.
    /// Returns: self-mapping status.
    fn validate_self_mapping(&self, paddr: PhysAddr, vaddr: VirtAddr) -> Result<(), PagingError> {
        let mapping = self.root().walk(vaddr);
        let level = mapping.level();
        let entry = mapping.observed();
        let translated =
            (entry.address() & !(level.size() - 1)) + (vaddr.bits() & (level.size() - 1));
        if !entry.is_present_leaf(level) || translated != paddr.bits() {
            return Err(PagingError::TablePageNotSelfMapped);
        }
        Ok(())
    }

    /// Inputs: current typed table.
    /// Requires: stable leveled tree.
    /// Returns: child validation.
    fn validate_child_tables<PL: WalkLevelImpl>(
        &self,
        page: PTPagePointer<'_, A, P, PL>,
    ) -> Result<(), PagingError> {
        for idx in 0..PT_ENTRY_COUNT {
            let entry = page.load(idx);
            if !entry.is_present_table(PL::LEVEL) {
                continue;
            }
            self.validate_page::<PL::ChildLevel>(PhysAddr::from(entry.address()))?;
        }
        Ok(())
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
    pub(crate) fn root_paddr(&self) -> PhysAddr {
        self.root
    }

    pub(crate) fn policy(&self) -> &S {
        &self.policy
    }

    pub(crate) fn root(&self) -> PTPagePointer<'_, A, P, L> {
        // SAFETY: the owner borrow pins the initialized tree and its reachable tables.
        unsafe { PTPagePointer::from_root(self.root) }
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
        self.root().grow_uninstalled(target_page, parent_flags)
    }
}

/// Inputs: entry index.
/// Requires: selected owned subtree.
/// Returns: true.
fn all_entries_owned(_: usize) -> bool {
    true
}

struct ReclaimPathVisitor<'a, F> {
    vaddr: VirtAddr,
    empty_entry: &'a F,
}

struct ReclaimRangeVisitor<'a, 'b, Owns, Empty> {
    start: usize,
    end: usize,
    owns_entry: &'a Owns,
    empty_entry: &'b Empty,
}

impl<'tree, A, P, F> PageLevelVisitor<'tree, A, P> for ReclaimPathVisitor<'_, F>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    F: Fn(PTEntry<A>) -> bool,
{
    type Output = (bool, usize);

    fn visit_l0(self, page: PTPagePointer<'tree, A, P, Lvl<0>>) -> Self::Output {
        (page.entries_satisfy(self.empty_entry), 0)
    }

    fn visit_l1(self, page: PTPagePointer<'tree, A, P, Lvl<1>>) -> Self::Output {
        unsafe { reclaim_path_inner(page, self.vaddr, self.empty_entry) }
    }

    fn visit_l2(self, page: PTPagePointer<'tree, A, P, Lvl<2>>) -> Self::Output {
        unsafe { reclaim_path_inner(page, self.vaddr, self.empty_entry) }
    }

    fn visit_l3(self, page: PTPagePointer<'tree, A, P, Lvl<3>>) -> Self::Output {
        unsafe { reclaim_path_inner(page, self.vaddr, self.empty_entry) }
    }

    fn visit_l4(self, page: PTPagePointer<'tree, A, P, Lvl<4>>) -> Self::Output {
        unsafe { reclaim_path_inner(page, self.vaddr, self.empty_entry) }
    }
}

impl<'tree, A, P, Owns, Empty> PageLevelVisitor<'tree, A, P>
    for ReclaimRangeVisitor<'_, '_, Owns, Empty>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    Owns: Fn(usize) -> bool,
    Empty: Fn(PTEntry<A>) -> bool,
{
    type Output = bool;

    fn visit_l0(self, page: PTPagePointer<'tree, A, P, Lvl<0>>) -> Self::Output {
        page.entries_satisfy(self.empty_entry)
    }

    fn visit_l1(self, page: PTPagePointer<'tree, A, P, Lvl<1>>) -> Self::Output {
        unsafe {
            reclaim_range_inner(page, self.start, self.end, self.owns_entry, self.empty_entry)
        }
    }

    fn visit_l2(self, page: PTPagePointer<'tree, A, P, Lvl<2>>) -> Self::Output {
        unsafe {
            reclaim_range_inner(page, self.start, self.end, self.owns_entry, self.empty_entry)
        }
    }

    fn visit_l3(self, page: PTPagePointer<'tree, A, P, Lvl<3>>) -> Self::Output {
        unsafe {
            reclaim_range_inner(page, self.start, self.end, self.owns_entry, self.empty_entry)
        }
    }

    fn visit_l4(self, page: PTPagePointer<'tree, A, P, Lvl<4>>) -> Self::Output {
        unsafe {
            reclaim_range_inner(page, self.start, self.end, self.owns_entry, self.empty_entry)
        }
    }
}

/// # Safety
/// The path must be exclusively owned and quiesced, without descendant
/// references surviving reclamation. `empty_entry` must reject every live mapping.
pub(crate) unsafe fn reclaim_path<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>(
    root: &PTPagePointer<'_, A, P, L>,
    vaddr: VirtAddr,
    empty_entry: impl Fn(PTEntry<A>) -> bool,
) -> usize {
    L::dispatch(root.duplicate(), ReclaimPathVisitor { vaddr, empty_entry: &empty_entry }).1
}

/// Inputs: root, address, and emptiness test.
/// Requires: exclusive path.
/// Returns: emptiness and count.
unsafe fn reclaim_path_inner<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>(
    root: PTPagePointer<'_, A, P, L>,
    vaddr: VirtAddr,
    empty_entry: &impl Fn(PTEntry<A>) -> bool,
) -> (bool, usize) {
    let index = entry_index(vaddr, root.level());
    let entry = root.load(index);
    let (child_pa, mut count) = match root.child_from_observed(entry) {
        Ok(child) => {
            let child_paddr = child.paddr();
            // SAFETY: the child inherits the caller's ownership and exclusion.
            let (empty, count) =
                L::ChildLevel::dispatch(child, ReclaimPathVisitor { vaddr, empty_entry });
            (empty.then_some(child_paddr), count)
        }
        Err(_) => (None, 0),
    };
    if let Some(paddr) = child_pa {
        root.swap(index, PTEntry::empty());
        // SAFETY: the child reference has ended and the parent no longer links it.
        unsafe { P::deallocate_table_page(paddr) };
        count += 1;
    }
    (root.entries_satisfy(empty_entry), count)
}

/// # Safety
/// The nonempty range must be within this root's local offsets. Selected
/// subtrees must be exclusively owned and quiesced, without surviving child
/// references. `empty_entry` must reject every live mapping; ownership applies
/// only to root entries, with every descendant owned.
pub(crate) unsafe fn reclaim_range<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>(
    root: &PTPagePointer<'_, A, P, L>,
    start: usize,
    end: usize,
    owns_entry: impl Fn(usize) -> bool,
    empty_entry: impl Fn(PTEntry<A>) -> bool,
) {
    L::dispatch(
        root.duplicate(),
        ReclaimRangeVisitor { start, end, owns_entry: &owns_entry, empty_entry: &empty_entry },
    );
}

/// Inputs: root, offsets, and predicates.
/// Requires: exclusive selected subtrees.
/// Returns: emptiness.
unsafe fn reclaim_range_inner<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>(
    root: PTPagePointer<'_, A, P, L>,
    start: usize,
    end: usize,
    owns_entry: &impl Fn(usize) -> bool,
    empty_entry: &impl Fn(PTEntry<A>) -> bool,
) -> bool {
    let size = root.level().size();
    for index in start / size..=(end - 1) / size {
        if !owns_entry(index) {
            continue;
        }
        let base = index * size;
        let entry = root.load(index);
        let child_pa = match root.child_from_observed(entry) {
            Ok(child) => {
                let child_paddr = child.paddr();
                // SAFETY: every descendant of the selected child is exclusively owned.
                let empty = L::ChildLevel::dispatch(
                    child,
                    ReclaimRangeVisitor {
                        start: start.saturating_sub(base),
                        end: (end - base).min(size),
                        owns_entry: &all_entries_owned,
                        empty_entry,
                    },
                );
                empty.then_some(child_paddr)
            }
            Err(_) => None,
        };
        if let Some(paddr) = child_pa {
            root.swap(index, PTEntry::empty());
            // SAFETY: no child reference or link remains when the empty page is freed.
            unsafe { P::deallocate_table_page(paddr) };
        }
    }
    root.entries_satisfy(empty_entry)
}
