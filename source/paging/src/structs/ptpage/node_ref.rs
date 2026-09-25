//! Lifetime-bound access to live page-table pages.
//!
//! Concurrent paging requires reads from a `PTPage` to coexist with writes to
//! its entries. Whole-page `&PTPage` and `&mut PTPage` borrows cannot express
//! that access pattern because the mutable borrow must be exclusive.
//! `PTPageRef` instead uses the tree lifetime only to pin the allocation
//! and grants no aliasing rights over entry contents. Each entry is observed or
//! changed through its atomic `PTEntryRef`, with writes separately serialized
//! by the controller when required.
use core::marker::PhantomData;
use core::ptr::NonNull;

use super::node::SplitRefreshLevel;
use super::tree::{
    PreserveSplitLeaf, SplitLeafChange, SplitLeafEncryption, SplitLeafFlags, StagedSplitLevel,
};
use super::{DetachedPageTable, PTPage, PTPageTree};
use crate::pagetable::LockSpec;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::{LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::PagingAllocator;
use crate::structs::os_contract::PagingError;
use crate::structs::page::Page;
use crate::structs::policy::KernelPolicy;
use crate::structs::sizes::PageSize;
use crate::structs::sizes::{entry_index, Huge, Regular, PT_ENTRY_COUNT};
use crate::structs::tlb::MayNeedFlush;

/// Pinned read access to one live page-table page.
pub(crate) struct PTPageRef<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> {
    page: NonNull<PTPage<A, P>>,
    marker: PhantomData<(&'tree PTPage<A, P>, L)>,
}

/// Tree-exclusive access for topology changes and reclamation.
pub(crate) struct PTPageMutRef<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> {
    page: NonNull<PTPage<A, P>>,
    marker: PhantomData<(&'tree mut PTPage<A, P>, L)>,
}

/// Software-exclusive, path-preserving updates to one live page.
///
/// Existing intermediate-table links cannot be replaced or removed. The
/// capability may update leaves, split a leaf, or publish a table into a
/// non-present
/// slot. Entry access remains atomic because hardware may update A/D bits.
pub(crate) struct PTPageUpdateRef<
    'lock,
    'tree,
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    WP: LockSpec<T>,
    T,
> where
    WP: 'lock,
    T: 'lock,
{
    page: NonNull<PTPage<A, P>>,
    _guard: WP::Guard<'lock>,
    marker: PhantomData<(&'lock PTPageRef<'tree, A, P, L>, T)>,
}

/// An atomic observation returned by a concurrent page-table walk.
pub struct WalkResult<A: ArchPagingMeta> {
    entry: PTEntry<A>,
    level: PageLevel,
}

type WalkStep<'tree, A, P, L> =
    Result<PTPageRef<'tree, A, P, <L as WalkLevelImpl>::ChildLevel>, WalkResult<A>>;

impl<A: ArchPagingMeta> WalkResult<A> {
    #[inline(always)]
    pub(crate) fn new(entry: PTEntry<A>, level: PageLevel) -> Self {
        Self { entry, level }
    }

    /// The level where the walk stopped.
    #[inline(always)]
    pub fn level(&self) -> PageLevel {
        self.level
    }

    /// The entry word observed by the walk.
    #[inline(always)]
    pub fn read(&self) -> PTEntry<A> {
        self.entry
    }
}

pub(crate) trait WalkLevelImpl: LevelSpec + Sized {
    type ChildLevel: WalkLevelImpl;

    fn erase_detached<'id, A: ArchPagingMeta, P: PagingAllocator>(
        tree: PTPageTree<A, P, Self, KernelPolicy, super::tree::Detached>,
    ) -> DetachedPageTable<'id, A, P>;
}

/// A supported static root level for [`crate::pagetable::PageTable`].
#[allow(private_bounds)]
pub trait WalkLevel: WalkLevelImpl {}

impl<L: WalkLevelImpl> WalkLevel for L {}

impl WalkLevelImpl for Lvl<0> {
    type ChildLevel = Lvl<0>;

    fn erase_detached<'id, A: ArchPagingMeta, P: PagingAllocator>(
        tree: PTPageTree<A, P, Self, KernelPolicy, super::tree::Detached>,
    ) -> DetachedPageTable<'id, A, P> {
        DetachedPageTable::from_l0(tree)
    }
}

impl WalkLevelImpl for Lvl<1> {
    type ChildLevel = Lvl<0>;

    fn erase_detached<'id, A: ArchPagingMeta, P: PagingAllocator>(
        tree: PTPageTree<A, P, Self, KernelPolicy, super::tree::Detached>,
    ) -> DetachedPageTable<'id, A, P> {
        DetachedPageTable::from_l1(tree)
    }
}

impl WalkLevelImpl for Lvl<2> {
    type ChildLevel = Lvl<1>;

    fn erase_detached<'id, A: ArchPagingMeta, P: PagingAllocator>(
        tree: PTPageTree<A, P, Self, KernelPolicy, super::tree::Detached>,
    ) -> DetachedPageTable<'id, A, P> {
        DetachedPageTable::from_l2(tree)
    }
}

impl WalkLevelImpl for Lvl<3> {
    type ChildLevel = Lvl<2>;

    fn erase_detached<'id, A: ArchPagingMeta, P: PagingAllocator>(
        tree: PTPageTree<A, P, Self, KernelPolicy, super::tree::Detached>,
    ) -> DetachedPageTable<'id, A, P> {
        DetachedPageTable::from_l3(tree)
    }
}

impl WalkLevelImpl for Lvl<4> {
    type ChildLevel = Lvl<3>;

    fn erase_detached<'id, A: ArchPagingMeta, P: PagingAllocator>(
        tree: PTPageTree<A, P, Self, KernelPolicy, super::tree::Detached>,
    ) -> DetachedPageTable<'id, A, P> {
        DetachedPageTable::from_l4(tree)
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> PTPageRef<'tree, A, P, L> {
    /// Locks this page and returns its path-preserving update capability.
    #[inline(always)]
    pub(crate) fn lock_to_update<'lock, WP, T>(
        &'lock self,
        wperms: &'lock WP,
    ) -> PTPageUpdateRef<'lock, 'tree, A, P, L, WP, T>
    where
        WP: LockSpec<T>,
        T: 'lock,
    {
        PTPageUpdateRef { page: self.page, _guard: wperms.lock(self.paddr()), marker: PhantomData }
    }

    /// # Safety
    /// `root_pa` must identify a table at `L`. The root and all reachable
    /// table pages and links must remain well-formed, initialized, writable and
    /// pinned for the views that can reach them.
    /// Entries must be atomic-aligned; conflicting accesses must be atomic,
    /// without ordinary references into live pages. Exclusive, quiesced teardown
    /// may reclaim descendants only after ending their views and unlinking them.
    pub(crate) unsafe fn from_root(root_pa: PhysAddr) -> Self {
        Self::resolve(root_pa)
    }

    #[inline(always)]
    fn resolve(paddr: PhysAddr) -> Self {
        let vaddr = P::paddr_to_vaddr(paddr);
        Self::from_vaddr(vaddr)
    }

    #[inline(always)]
    fn from_vaddr(vaddr: VirtAddr) -> Self {
        let page = vaddr.as_mut_ptr();
        Self { page: NonNull::new(page).expect("null page-table view"), marker: PhantomData }
    }

    #[inline(always)]
    pub(crate) fn level(&self) -> PageLevel {
        L::LEVEL
    }

    pub(crate) fn paddr(&self) -> PhysAddr {
        P::vaddr_to_paddr(VirtAddr::from(self.page.as_ptr() as usize))
    }

    #[inline(always)]
    pub(crate) fn walk(&self, vaddr: VirtAddr) -> WalkResult<A>
    where
        L: WalkLevelImpl,
    {
        self.walk_from(vaddr)
    }

    #[inline(always)]
    pub(super) fn entry(&self, index: usize) -> PTEntryRef<'tree, A> {
        assert!(index < PT_ENTRY_COUNT);
        // SAFETY: construction pins the page, and the checked entry remains within it.
        unsafe { self.page.as_ref() }.entry(index)
    }

    #[inline(always)]
    pub(crate) fn load(&self, index: usize) -> PTEntry<A> {
        self.entry(index).load()
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> PTPageMutRef<'tree, A, P, L> {
    /// # Safety
    /// `root_pa` must be an initialized, exclusively tree-owned page at `L`.
    pub(super) unsafe fn from_root(root_pa: PhysAddr) -> Self {
        let vaddr = P::paddr_to_vaddr(root_pa);
        let page = NonNull::new(vaddr.as_mut_ptr()).expect("null page-table view");
        Self { page, marker: PhantomData }
    }

    #[inline(always)]
    pub(crate) fn level(&self) -> PageLevel {
        L::LEVEL
    }

    #[inline(always)]
    pub(crate) fn load(&self, index: usize) -> PTEntry<A> {
        assert!(index < PT_ENTRY_COUNT);
        unsafe { self.page.as_ref() }.entry(index).load()
    }

    pub(crate) fn store(&mut self, index: usize, value: PTEntry<A>) {
        assert!(index < PT_ENTRY_COUNT);
        unsafe { self.page.as_ref() }.entry(index).store(value);
    }

    pub(crate) fn swap(&mut self, index: usize, value: PTEntry<A>) -> PTEntry<A> {
        assert!(index < PT_ENTRY_COUNT);
        unsafe { self.page.as_ref() }.entry(index).swap(value)
    }

    pub(super) fn entries_clear(&self) -> bool {
        (0..PT_ENTRY_COUNT).all(|index| self.load(index).is_clear())
    }
}

impl<'lock, 'tree, A, P, L, WP, T> PTPageUpdateRef<'lock, 'tree, A, P, L, WP, T>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    WP: LockSpec<T> + 'lock,
    T: 'lock,
{
    #[inline(always)]
    fn entry(&mut self, index: usize) -> PTEntryRef<'_, A> {
        assert!(index < PT_ENTRY_COUNT);
        // SAFETY: the source PTPageRef pins this page for the write capability's lifetime.
        unsafe { self.page.as_ref() }.entry(index)
    }

    fn leaf_for_update(
        &mut self,
        index: usize,
        target: PageLevel,
    ) -> Result<(PTEntryRef<'_, A>, PTEntry<A>), PagingError> {
        if L::LEVEL < target {
            return Err(PagingError::NotLeafEntry);
        }
        let pte_ref = self.entry(index);
        let current = pte_ref.load();
        if current.is_present_leaf(L::LEVEL) {
            Ok((pte_ref, current))
        } else if current.is_present_table(L::LEVEL) {
            Err(PagingError::NotLeafEntry)
        } else {
            Err(PagingError::NotMapped)
        }
    }

    #[inline(always)]
    /// Atomically reads one locked entry.
    pub(crate) fn load(&self, index: usize) -> PTEntry<A> {
        assert!(index < PT_ENTRY_COUNT);
        // SAFETY: the source PTPageRef pins this page for the write capability's lifetime.
        unsafe { self.page.as_ref() }.entry(index).load()
    }

    /// Installs a leaf only when no leaf or table occupies the slot.
    pub(crate) fn install_leaf(
        &mut self,
        index: usize,
        value: PTEntry<A>,
    ) -> Result<(), PagingError> {
        let current = self.load(index);
        if current.is_table(L::LEVEL) {
            return Err(PagingError::NotLeafEntry);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level: L::LEVEL });
        }
        self.entry(index).store(value);
        Ok(())
    }

    /// Publishes a child table only when the slot remains non-present.
    pub(crate) fn publish_table(
        &mut self,
        index: usize,
        value: PTEntry<A>,
    ) -> Result<(), PagingError> {
        if L::LEVEL.is_leaf() || !value.is_present_table(L::LEVEL) {
            return Err(PagingError::InvalidLevel);
        }
        let current = self.load(index);
        if current.present() {
            return if current.is_table(L::LEVEL) {
                Err(PagingError::NotLeafEntry)
            } else {
                Err(PagingError::EntryAlreadyPresent { level: L::LEVEL })
            };
        }
        self.entry(index).store(value);
        Ok(())
    }

    /// Removes a present leaf without changing an intermediate-table link.
    pub(crate) fn take_leaf(&mut self, index: usize) -> Result<Option<PTEntry<A>>, PagingError> {
        let current = self.load(index);
        if current.is_table(L::LEVEL) {
            return Err(PagingError::NotLeafEntry);
        }
        if !current.present() {
            return Ok(None);
        }
        Ok(Some(self.entry(index).swap(PTEntry::empty())))
    }

    /// Replaces flags on a present leaf and returns whether it changed.
    pub(crate) fn set_leaf_flags(
        &mut self,
        index: usize,
        flags: A::PTFlags,
    ) -> Result<bool, PagingError> {
        let current = self.load(index);
        if !current.is_present_leaf(L::LEVEL) {
            return Err(PagingError::NotMapped);
        }
        let mut desired = current;
        PTPage::<A, P>::set_leaf_flags(&mut desired, flags);
        if desired.raw() == current.raw() {
            return Ok(false);
        }
        self.entry(index).update_valid_entry(current, desired);
        Ok(true)
    }

    /// Splits one locked leaf down to `PS`.
    ///
    /// # Safety
    /// The selected entry must stay pinned with software writers excluded.
    pub(crate) unsafe fn split_leaf_to<PS: PageSize>(
        &mut self,
        index: usize,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        if L::LEVEL == PS::LEVEL {
            return Ok(MayNeedFlush::none());
        }
        let (pte_ref, current) = self.leaf_for_update(index, PS::LEVEL)?;
        match L::LEVEL {
            PageLevel::Level1 => unsafe {
                publish_leaf_split::<A, P, Lvl<1>, _, _>(
                    pte_ref,
                    current,
                    page,
                    PreserveSplitLeaf,
                    all_cpus,
                )
            },
            PageLevel::Level2 => unsafe {
                publish_leaf_split::<A, P, Lvl<2>, _, _>(
                    pte_ref,
                    current,
                    page,
                    PreserveSplitLeaf,
                    all_cpus,
                )
            },
            _ => Err(PagingError::InvalidLevel),
        }
    }

    /// Splits the locked region leaf by one level.
    ///
    /// # Safety
    /// The selected entry must stay pinned with software writers excluded.
    pub(crate) unsafe fn split_leaf_for_region(
        &mut self,
        index: usize,
        vaddr: VirtAddr,
    ) -> Result<(), PagingError> {
        match L::LEVEL {
            PageLevel::Level1 => unsafe {
                self.split_leaf_to(index, Page::<Regular>::containing_address(vaddr), true)
            },
            PageLevel::Level2 => unsafe {
                self.split_leaf_to(index, Page::<Huge>::containing_address(vaddr), true)
            },
            _ => Err(PagingError::InvalidLevel),
        }
        .map(|_| ())
    }
}

/// # Safety
/// `pte_ref` must stay pinned with software writers excluded.
unsafe fn publish_leaf_split<A, P, L, PS, C>(
    pte_ref: PTEntryRef<'_, A>,
    current: PTEntry<A>,
    target_page: Page<PS>,
    change: C,
    all_cpus: bool,
) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: StagedSplitLevel + SplitRefreshLevel,
    L::Child: WalkLevelImpl,
    PS: PageSize,
    C: SplitLeafChange<A>,
{
    let tree = PTPageTree::<A, P, L>::new_split(current, target_page, change, KernelPolicy::new())?;
    unsafe {
        PTPage::<A, P>::publish_prepared_split::<L, PS, C>(
            pte_ref,
            current,
            target_page,
            change,
            tree,
            all_cpus,
        )
    }
}

impl<'lock, 'tree, A, P, L, WP, T> PTPageUpdateRef<'lock, 'tree, A, P, L, WP, T>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevelImpl,
    WP: LockSpec<T> + 'lock,
    T: 'lock,
{
    /// Changes one locked leaf's shared/private address tag.
    ///
    /// # Safety
    /// The selected entry must stay pinned with software writers excluded.
    pub(crate) unsafe fn set_encryption_at<PS: PageSize>(
        &mut self,
        index: usize,
        page: Page<PS>,
        shared: bool,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let level = L::LEVEL;
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let (pte_ref, current) = self.leaf_for_update(index, target)?;
        if level > target {
            return match level {
                PageLevel::Level1 => unsafe {
                    publish_leaf_split::<A, P, Lvl<1>, _, _>(
                        pte_ref,
                        current,
                        page,
                        SplitLeafEncryption(shared),
                        all_cpus,
                    )
                },
                PageLevel::Level2 => unsafe {
                    publish_leaf_split::<A, P, Lvl<2>, _, _>(
                        pte_ref,
                        current,
                        page,
                        SplitLeafEncryption(shared),
                        all_cpus,
                    )
                },
                _ => Err(PagingError::InvalidLevel),
            };
        }

        Ok(unsafe {
            PTPage::<A, P>::replace_leaf_encryption::<PS>(pte_ref, current, vaddr, shared, all_cpus)
        })
    }

    /// Replaces flags in one locked leaf, splitting privately when needed.
    ///
    /// # Safety
    /// The selected entry must stay pinned with software writers excluded.
    #[inline(always)]
    pub(crate) unsafe fn update_leaf_flags_at<PS: PageSize>(
        &mut self,
        index: usize,
        page: Page<PS>,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let level = L::LEVEL;
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let (pte_ref, current) = self.leaf_for_update(index, target)?;
        let flags = A::filter_flags(flags);
        if level > target {
            return match level {
                PageLevel::Level1 => unsafe {
                    publish_leaf_split::<A, P, Lvl<1>, _, _>(
                        pte_ref,
                        current,
                        page,
                        SplitLeafFlags(flags),
                        all_cpus,
                    )
                },
                PageLevel::Level2 => unsafe {
                    publish_leaf_split::<A, P, Lvl<2>, _, _>(
                        pte_ref,
                        current,
                        page,
                        SplitLeafFlags(flags),
                        all_cpus,
                    )
                },
                _ => Err(PagingError::InvalidLevel),
            };
        }
        // SAFETY: the caller excludes writers and `current` is the locked leaf snapshot.
        Ok(unsafe {
            PTPage::<A, P>::update_leaf_flags_in_place(pte_ref, current, level, vaddr, flags)
        })
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> PTPageRef<'tree, A, P, L> {
    #[inline(always)]
    fn walk_from(&self, vaddr: VirtAddr) -> WalkResult<A> {
        match self.step_at(vaddr) {
            Ok(child) => child.walk_from(vaddr),
            Err(result) => result,
        }
    }

    // Keep this inlined: its combined table test gives the unrolled walk one hot-path branch.
    #[inline(always)]
    fn step_at(&self, vaddr: VirtAddr) -> WalkStep<'tree, A, P, L> {
        let level = self.level();
        let index = entry_index(vaddr, level);
        let observed = self.load(index);
        if observed.is_present_table(level) {
            let paddr = PhysAddr::from(observed.address());
            Ok(PTPageRef::resolve(paddr))
        } else {
            Err(WalkResult::new(observed, level))
        }
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> PTPageRef<'tree, A, P, L> {
    /// Resolves the observed child table without reloading its parent entry.
    #[inline(always)]
    pub(crate) fn child_from_observed(
        &self,
        entry: PTEntry<A>,
    ) -> Result<PTPageRef<'tree, A, P, L::ChildLevel>, PTEntry<A>> {
        if entry.is_present_table(self.level()) {
            Ok(PTPageRef::resolve(PhysAddr::from(entry.address())))
        } else {
            Err(entry)
        }
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> PTPageMutRef<'tree, A, P, L> {
    pub(super) fn child_from_observed(
        &mut self,
        entry: PTEntry<A>,
    ) -> Result<PTPageMutRef<'_, A, P, L::ChildLevel>, PTEntry<A>> {
        if entry.is_present_table(self.level()) {
            // SAFETY: the mutable parent-tree borrow exclusively covers its child topology.
            Ok(unsafe { PTPageMutRef::from_root(PhysAddr::from(entry.address())) })
        } else {
            Err(entry)
        }
    }

    /// Detaches empty tables on one path and emits ownership to `detached`.
    pub(crate) fn detach_path<'id>(
        &mut self,
        vaddr: VirtAddr,
        detached: &mut impl FnMut(DetachedPageTable<'id, A, P>),
    ) -> usize {
        self.detach_path_from(vaddr, detached).1
    }

    fn detach_path_from<'id>(
        &mut self,
        vaddr: VirtAddr,
        detached: &mut impl FnMut(DetachedPageTable<'id, A, P>),
    ) -> (bool, usize) {
        if L::LEVEL == PageLevel::Level0 {
            return (self.entries_clear(), 0);
        }
        let index = entry_index(vaddr, self.level());
        let entry = self.load(index);
        let (child_empty, mut count) = match self.child_from_observed(entry) {
            Ok(mut child) => {
                let (empty, count) = child.detach_path_from(vaddr, detached);
                (empty, count)
            }
            Err(_) => (false, 0),
        };
        if child_empty {
            let tree = self
                .detach_subtree(index)
                .unwrap_or_else(|_| unreachable!("reclaimed child must remain a table"));
            detached(tree.erase());
            count += 1;
        }
        (self.entries_clear(), count)
    }

    pub(crate) fn detach_range_chunk<'id>(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        owned_root_mask: &[u64; PT_ENTRY_COUNT / 64],
        detached: &mut [Option<DetachedPageTable<'id, A, P>>],
    ) -> (usize, bool) {
        assert!(detached.iter().all(Option::is_none));
        let mut count = 0;
        let size = self.level().size();
        let last = (end.bits() - 1) / size;
        let mut index = start.bits() / size;
        while index <= last {
            while index <= last && owned_root_mask[index / 64] & (1 << (index % 64)) == 0 {
                index += 1;
            }
            if index > last {
                break;
            }
            let first_owned = index;
            while index <= last && owned_root_mask[index / 64] & (1 << (index % 64)) != 0 {
                index += 1;
            }
            let owned_start = start.bits().max(first_owned * size);
            let owned_end = end.bits().min(index * size);
            let (_, complete) = self.detach_range_from(
                VirtAddr::from(owned_start),
                VirtAddr::from(owned_end),
                detached,
                &mut count,
            );
            if !complete {
                return (count, false);
            }
        }
        (count, true)
    }

    fn detach_range_from<'id>(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        detached: &mut [Option<DetachedPageTable<'id, A, P>>],
        count: &mut usize,
    ) -> (bool, bool) {
        if L::LEVEL == PageLevel::Level0 {
            return (self.entries_clear(), true);
        }
        let size = self.level().size();
        for index in start.bits() / size..=(end.bits() - 1) / size {
            if *count == detached.len() {
                return (false, false);
            }
            let base = index * size;
            let entry = self.load(index);
            let (child_empty, complete) = match self.child_from_observed(entry) {
                Ok(mut child) => child.detach_range_from(
                    VirtAddr::from(start.bits().saturating_sub(base)),
                    VirtAddr::from((end.bits() - base).min(size)),
                    detached,
                    count,
                ),
                Err(_) => (false, true),
            };
            if !complete {
                return (false, false);
            }
            if child_empty {
                if *count == detached.len() {
                    return (false, false);
                }
                let tree = self
                    .detach_subtree(index)
                    .unwrap_or_else(|_| unreachable!("reclaimed child must remain a table"));
                detached[*count] = Some(tree.erase());
                *count += 1;
            }
        }
        (self.entries_clear(), true)
    }

    /// Clears selected entries and frees their descendant tables, not data frames.
    /// # Safety
    /// Hardware must be quiesced, and all descendants must belong to `P`.
    pub(crate) unsafe fn free_children(&mut self, owns_entry: impl Fn(usize) -> bool) {
        let mut reclaim = |tree: DetachedPageTable<'_, A, P>| {
            // SAFETY: the free caller guarantees hardware synchronization.
            drop(unsafe { tree.into_staged_after_flush_unchecked() });
        };
        self.detach_children(owns_entry, &mut reclaim);
    }

    /// Detaches selected child subtrees and clears selected leaf entries.
    pub(crate) fn detach_children<'id>(
        &mut self,
        owns_entry: impl Fn(usize) -> bool,
        detached: &mut impl FnMut(DetachedPageTable<'id, A, P>),
    ) {
        for index in 0..PT_ENTRY_COUNT {
            if !owns_entry(index) {
                continue;
            }
            let entry = self.load(index);
            if entry.is_present_table(L::LEVEL) {
                let tree = self
                    .detach_subtree(index)
                    .unwrap_or_else(|_| unreachable!("observed table must remain a table"));
                detached(tree.erase());
            } else {
                self.swap(index, PTEntry::empty());
            }
        }
    }

    pub(super) fn grow_uninstalled<PS: PageSize>(
        &mut self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        self.grow_from(target_page, parent_flags)
    }

    pub(super) fn store_uninstalled<PS: PageSize>(
        &mut self,
        target_page: Page<PS>,
        value: PTEntry<A>,
    ) -> Result<(), PagingError> {
        if L::LEVEL < PS::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        let index = entry_index(target_page.start_address(), L::LEVEL);
        if L::LEVEL == PS::LEVEL {
            self.store(index, value);
            return Ok(());
        }
        let entry = self.load(index);
        let mut child = self.child_from_observed(entry).map_err(|_| PagingError::NotLeafEntry)?;
        child.store_uninstalled(target_page, value)
    }

    #[inline(always)]
    fn grow_from<PS: PageSize>(
        &mut self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        if L::LEVEL == PS::LEVEL {
            return Ok(());
        }
        let index = entry_index(target_page.start_address(), self.level());
        let entry = self.load(index);
        match self.child_from_observed(entry) {
            Ok(mut child) => child.grow_from(target_page, parent_flags),
            Err(entry) if entry.present() => Err(PagingError::NotLeafEntry),
            Err(_) => {
                let mut child = PTPageTree::<A, P, L::ChildLevel>::new_root(KernelPolicy::new())?;
                child.root_mut().grow_from(target_page, parent_flags)?;
                self.store(
                    index,
                    PTEntry::new_table(A::make_private_address(child.root_paddr()), parent_flags),
                );
                child.release();
                Ok(())
            }
        }
    }
}
