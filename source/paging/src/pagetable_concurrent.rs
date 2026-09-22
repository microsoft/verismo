//! The `pagetable` API with concurrent walks and serialized entry updates.
//! Shared borrows pin table pages; exclusive borrows permit reclamation.
//! An external RwLock can provide those borrows. It does not fence hardware
//! walkers: the embedder supplies synchronous TLB hooks and hardware quiescence.
#![doc = include_str!("../concurrency.md")]

use core::marker::PhantomData;
use core::ops::ControlFlow;
use core::ops::{Deref, DerefMut};

use crate::structs::address::{Address, PhysAddr, VirtAddr, LOW_CANONICAL_END};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::{
    DirectMappedAllocator, MapRegionError, PagingAllocator, PagingError,
};
use crate::structs::page::{Page, PageRangeInclusive};
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy, RootEntrySet, UserPolicy};
use crate::structs::ptpage::{
    reclaim_path, reclaim_range, FlushFootprint, LeafSplitLevelImpl, Live, Mapping, PTPage,
    PTPagePointer, PTPageTree, StableInnerVisit, StableVisitor, Translation, WalkLevel,
    WalkLevelImpl, WalkPosition, WalkResult,
};
use crate::structs::sizes::{entry_index, Huge, PageSize, Regular, SizeLevel2, PT_ENTRY_COUNT};
use crate::structs::tlb::{MayNeedFlush, TlbFlush};

/// A removed entry paired with any TLB invalidation it leaves outstanding.
pub type UnmapEntryResult<A> =
    Result<(Option<PTEntry<A>>, MayNeedFlush<<A as ArchPagingMeta>::TlbFlushTok>), PagingError>;

struct RangeUnmapState<'a> {
    all_mapped: &'a mut bool,
    footprint: &'a mut FlushFootprint,
}

struct UnmapRegionVisitor<'a, 'state, Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    Owned: PagingOwnershipPolicy,
{
    table: &'a PageTable<Arch, Alloc, MaxLevel, WP, T, Owned>,
    state: &'a mut RangeUnmapState<'state>,
}

struct RangeFlagsState<T: TlbFlush> {
    cursor: usize,
    flush: MayNeedFlush<T>,
    footprint: FlushFootprint,
    descents_left: usize,
    descent_cursor: usize,
    partial_leaves_left: usize,
}

type RangeFlagsResult<T> = (Result<(), PagingError>, MayNeedFlush<T>);

impl<'tree, Arch, Alloc, MaxLevel, WP, T, Owned> StableVisitor<'tree, Arch, Alloc>
    for UnmapRegionVisitor<'_, '_, Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Owned: PagingOwnershipPolicy,
{
    type Break = PagingError;

    #[inline(always)]
    fn visit_l0(
        &mut self,
        page: PTPagePointer<'tree, Arch, Alloc, Lvl<0>>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break> {
        let level = PageLevel::Level0;
        let first = entry_index(VirtAddr::from(start), level);
        let last = entry_index(VirtAddr::from(end - 1), level);
        let mut first_changed = None;
        let mut last_changed = start;
        let mut cursor = start;
        let _guard = self.table.wperms.lock(page_paddr.unwrap_or_else(|| page.paddr()));
        for index in first..=last {
            let pte_ref = page.entry(index);
            if pte_ref.load().is_present_leaf(level) {
                pte_ref.swap(PTEntry::empty());
                first_changed.get_or_insert(cursor);
                last_changed = cursor;
            } else {
                *self.state.all_mapped = false;
            }
            cursor = cursor.saturating_add(level.size());
        }
        if let Some(first) = first_changed {
            self.state.footprint.include(VirtAddr::from(first), level);
            self.state.footprint.include(VirtAddr::from(last_changed), level);
        }
        ControlFlow::Continue(())
    }

    fn visit_l0_entry(
        &mut self,
        page: &PTPagePointer<'tree, Arch, Alloc, Lvl<0>>,
        page_paddr: PhysAddr,
        index: usize,
        _: PTEntry<Arch>,
        start: usize,
        _: usize,
    ) -> ControlFlow<Self::Break> {
        let pte_ref = page.entry(index);
        let _guard = self.table.wperms.lock(page_paddr);
        let current = pte_ref.load();
        if current.is_present_leaf(PageLevel::Level0) {
            pte_ref.swap(PTEntry::empty());
            self.state.footprint.include(VirtAddr::from(start), PageLevel::Level0);
        } else {
            *self.state.all_mapped = false;
        }
        ControlFlow::Continue(())
    }

    fn visit_inner_entry<L: InnerLevel + LeafSplitLevelImpl + WalkLevelImpl>(
        &mut self,
        page: &PTPagePointer<'tree, Arch, Alloc, L>,
        page_paddr: PhysAddr,
        index: usize,
        _: PTEntry<Arch>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break, StableInnerVisit<'tree, Arch, Alloc, L>>
    where
        L::Child: WalkLevelImpl,
    {
        let level = L::LEVEL;
        let pte_ref = page.entry(index);
        let _guard = self.table.wperms.lock(page_paddr);
        let current = pte_ref.load();
        if current.is_present_table(level) {
            return ControlFlow::Continue(StableInnerVisit::descend(page, current));
        }
        if !current.is_present_leaf(level) {
            *self.state.all_mapped = false;
            return ControlFlow::Continue(StableInnerVisit::Continue);
        }
        let start = VirtAddr::from(start);
        if start.is_aligned(level.size()) && end - start.bits() >= level.size() {
            pte_ref.swap(PTEntry::empty());
            self.state.footprint.include(start, level);
            return ControlFlow::Continue(StableInnerVisit::Continue);
        }

        // SAFETY: the content guard pins the entry and excludes competing writers.
        match unsafe { L::split_leaf_for_region::<Arch, Alloc>(pte_ref, start) } {
            Ok(()) => {
                let child = pte_ref.load();
                ControlFlow::Continue(StableInnerVisit::descend(page, child))
            }
            Err(error) => ControlFlow::Break(error),
        }
    }
}

impl<T: TlbFlush> RangeFlagsState<T> {
    /// Inputs: final result.
    /// Requires: completed updates.
    /// Returns: result with accumulated flush.
    fn finish(&mut self, result: Result<(), PagingError>) -> RangeFlagsResult<T> {
        let flush = core::mem::replace(&mut self.flush, MayNeedFlush::none());
        (result, flush.and(self.footprint.token()))
    }
}

/// Arch write-permission lock keyed by physical table page. Keys may share one lock or
/// select per-page/striped locks; paging never holds two guards at once.
/// Guards borrow protected metadata/permissions, never live PTE storage.
///
/// # Safety
/// Guards for the same page must exclude each other, acquiring on `lock` and
/// releasing on drop without panicking. Keys and exclusion must remain stable
/// across every tree sharing those pages, including during unwinding.
pub unsafe trait LockSpec<T> {
    /// Arch borrowed guard excluding writers for one keyed table page.
    type Guard<'a>: Deref<Target = T> + DerefMut
    where
        Self: 'a,
        T: 'a;

    /// Inputs: table address.
    /// Requires: stable lock domain.
    /// Returns: exclusive write guard.
    fn lock(&self, page: PhysAddr) -> Self::Guard<'_>;
}

/// Internal outcome used to restart a range walk after a concurrent split.
enum RangeUpdateError {
    Descend,
    Split(usize, PageLevel),
    Paging(PagingError),
}

/// Shared access permits walk, map, unmap and split, but never removes an
/// installed table pointer. Freeing needs `&mut self` and hardware exclusion.
/// Drop frees the root and owned descendant tables, never shared subtrees or data
/// frames. Externally managed or hardware-active trees need `ManuallyDrop` or `leak`.
pub struct PageTable<
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP,
    T = (),
    Owned: PagingOwnershipPolicy = KernelPolicy,
> {
    tree: PTPageTree<Arch, Alloc, MaxLevel, Owned, Live>,
    wperms: WP,
    marker: PhantomData<T>,
}

/// Arch concurrent kernel page table using `WP` as its PTE write-permission domain.
pub type KernelPageTable<Arch, Alloc, MaxLevel, WP, T = ()> =
    PageTable<Arch, Alloc, MaxLevel, WP, T, KernelPolicy>;
/// Arch concurrent user page table borrowing the configured kernel root entries.
pub type UserPageTable<'kernel, Arch, Alloc, MaxLevel, WP, Reserved, T = ()> =
    PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<'kernel, Reserved>>;

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: DirectMappedAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
{
    /// Direct-maps the allocator's region with ordinary memory accesses:
    /// construction has no concurrent readers and takes no content locks.
    pub fn new(wperms: WP, flags: Arch::PTFlags) -> Result<Self, PagingError> {
        let tree = PTPageTree::new_direct_mapped(flags)?;
        tree.validate()?;
        let tree = tree.into_live();
        Ok(Self { tree, wperms, marker: PhantomData })
    }
}

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
{
    /// Validates an existing root before constructing its controller.
    /// Rejection or validation unwinding leaves the root allocated.
    /// # Safety
    /// Keep the initialized, correctly leveled, acyclic tree at clean `root_pa`
    /// accessible and aligned for `PTPage` for this controller's lifetime.
    /// Every software user must follow this atomic-access, content-lock and
    /// lifetime protocol. Shared pages must
    /// appear at identical virtual prefixes, never at different aliases.
    /// Only allow Drop when the root and every descendant table are exclusively
    /// owned, allocator-allocated, and have no software or hardware users;
    /// otherwise use `ManuallyDrop` or [`Self::leak`].
    pub unsafe fn from_root(wperms: WP, root_pa: PhysAddr) -> Result<Self, PagingError> {
        // SAFETY: tree accessibility and ownership are required by this constructor.
        let tree =
            unsafe { PTPageTree::<Arch, Alloc, MaxLevel, KernelPolicy>::from_root(root_pa) }?
                .into_live();
        Ok(Self { tree, wperms, marker: PhantomData })
    }

    /// Borrows the root entries selected by `Reserved`; those entries become
    /// immutable. `wperms` protects only independently owned entries.
    /// # Safety
    /// Shared descendants must remain allocated while the returned table or any
    /// leaked root derived from it can be used.
    pub unsafe fn new_from_sharing_top<'kernel, Reserved: RootEntrySet>(
        wperms: WP,
        other: &'kernel Self,
    ) -> Result<UserPageTable<'kernel, Arch, Alloc, MaxLevel, WP, Reserved, T>, PagingError> {
        let policy = UserPolicy::<Reserved>::new();
        let tree = PTPageTree::new_root(policy)?.into_live();
        let root = tree.root();
        for idx in (0..PT_ENTRY_COUNT).filter(|index| Reserved::contains(*index)) {
            let entry = other.root_view().load(idx);
            if entry.is_present_table(MaxLevel::LEVEL) {
                root.store(idx, entry);
            }
        }
        tree.validate()?;
        Ok(PageTable { tree, wperms, marker: PhantomData })
    }

    /// Gives up the tree and returns its root and content-lock domain.
    /// Arch borrowed root remains borrowed; its ownership is not transferred.
    pub fn leak(self) -> (WP, PhysAddr) {
        let (wperms, _, root_pa) = self.leak_parts();
        (wperms, root_pa)
    }
}

impl<'kernel, Arch, Alloc, MaxLevel, WP, T, Reserved>
    PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<'kernel, Reserved>>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Reserved: RootEntrySet,
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak(self) -> (WP, UserPolicy<'kernel, Reserved>, PhysAddr) {
        self.leak_parts()
    }
}

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Owned: PagingOwnershipPolicy,
{
    const SMALL: PageLevel = PageLevel::Level0;

    /// Inputs: owned controller.
    /// Requires: none.
    /// Returns: lock, policy, and unreclaimed root.
    fn leak_parts(self) -> (WP, Owned, PhysAddr) {
        let (policy, root_pa) = self.tree.into_parts();
        (self.wperms, policy, root_pa)
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    /// Inputs: controller borrow.
    /// Requires: live tree.
    /// Returns: pinned atomic root view.
    fn root_view(&self) -> PTPagePointer<'_, Arch, Alloc, MaxLevel> {
        self.tree.root()
    }

    /// Arch leaf/absent-entry snapshot. It holds no content lock and gives no
    /// authority to dereference or free the translated data frame.
    #[inline(always)]
    pub fn walk(&self, vaddr: VirtAddr) -> WalkResult<Arch> {
        let position = self.tree.root().walk(vaddr);
        WalkResult::new(position.observed(), position.level())
    }

    /// Inputs: page, frame, and flags.
    /// Requires: valid typed mapping.
    /// Returns: mapping status.
    #[inline(always)]
    fn do_map<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let paddr = frame.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        // This implementation supports mappings only through the 1 GiB leaf level.
        if target > PageLevel::Level2 || target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        // Mapping a non-present entry would create an inaccessible leaf.
        assert!(flags.present());
        let flags = Arch::filter_flags(flags);
        let parent_flags = Arch::filter_flags(parent_flags);
        let addr = if shared {
            Arch::make_shared_address(paddr)
        } else {
            Arch::make_private_address(paddr)
        };
        let flags = if target.is_leaf() { flags } else { flags.with(Arch::PTFlags::HUGE) };
        let leaf = PTEntry::new(addr, flags);
        let mut mapping = self.root_view().walk(vaddr);
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let level = mapping.level();
            // A finer existing subtree cannot hold the requested larger leaf.
            if level < target {
                return Err(PagingError::NotLeafEntry);
            }
            // At the target level only the leaf slot itself remains to be installed.
            if level == target {
                return self.install_leaf(&mapping, leaf);
            }
            // Follow an intermediate table observed by this walk.
            if mapping.observed().is_present_table(level) {
                mapping = mapping.walk(vaddr);
                continue;
            }
            // A present larger leaf blocks creation of the requested finer mapping.
            if mapping.observed().present() {
                return Err(PagingError::EntryAlreadyPresent { level });
            }
            // A new private subtree already contains the requested leaf.
            if self.alloc_and_install_leaf(&mapping, page, parent_flags, leaf)? {
                return Ok(());
            }
            // Another thread published this shared parent while mapping this or
            // another virtual address, so continue through the winning table.
            mapping = mapping.walk(vaddr);
        }
        unreachable!("mapping traversal exceeded the page-table depth")
    }

    /// Installs `leaf` if the locked slot is clear and not an invalidated child table.
    fn install_leaf(
        &self,
        mapping: &WalkPosition<'_, Arch, Alloc>,
        leaf: PTEntry<Arch>,
    ) -> Result<(), PagingError> {
        let level = mapping.level();
        let _guard = self.wperms.lock(mapping.page_paddr());
        let pte_ref = mapping.entry();
        let entry = pte_ref.load();
        // A concurrent split may leave a child table temporarily non-present during BBM.
        if entry.is_table(level) {
            return Err(PagingError::NotLeafEntry);
        }
        // A concurrent map may have installed a leaf after the walk observed this slot.
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }
        pte_ref.store(leaf);
        Ok(())
    }

    /// Prepares the missing subtree and publishes it if the parent slot remains absent.
    /// Returns `false` when another thread publishes the shared parent first.
    fn alloc_and_install_leaf<PS: PageSize>(
        &self,
        mapping: &WalkPosition<'_, Arch, Alloc>,
        page: Page<PS>,
        parent_flags: Arch::PTFlags,
        leaf: PTEntry<Arch>,
    ) -> Result<bool, PagingError> {
        match mapping {
            WalkPosition::Level0(_) => Err(PagingError::InvalidLevel),
            WalkPosition::Level1(stop) => {
                self.alloc_and_install_leaf_at(&stop.page, stop.index, page, parent_flags, leaf)
            }
            WalkPosition::Level2(stop) => {
                self.alloc_and_install_leaf_at(&stop.page, stop.index, page, parent_flags, leaf)
            }
            WalkPosition::Level3(stop) => {
                self.alloc_and_install_leaf_at(&stop.page, stop.index, page, parent_flags, leaf)
            }
            WalkPosition::Level4(stop) => {
                self.alloc_and_install_leaf_at(&stop.page, stop.index, page, parent_flags, leaf)
            }
        }
    }

    /// Builds and publishes a typed child subtree for one absent parent slot.
    fn alloc_and_install_leaf_at<PS: PageSize, L: WalkLevelImpl>(
        &self,
        parent: &PTPagePointer<'_, Arch, Alloc, L>,
        index: usize,
        page: Page<PS>,
        parent_flags: Arch::PTFlags,
        leaf: PTEntry<Arch>,
    ) -> Result<bool, PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let level = L::LEVEL;
        let mut prepared = PTPageTree::<Arch, Alloc, L::ChildLevel>::new_root(KernelPolicy)?;
        prepared.grow(page, parent_flags)?;
        let prepared_mapping = prepared.root().walk(vaddr);
        debug_assert_eq!(prepared_mapping.level(), target);
        prepared_mapping.entry().store(leaf);

        let _guard = self.wperms.lock(parent.paddr());
        let pte_ref = parent.entry(index);
        let current = pte_ref.load();
        // A concurrent map may publish the shared parent first; its subtree may
        // contain a different virtual address, so the caller must follow it.
        if current.is_present_table(level) {
            return Ok(false);
        }
        // A concurrent larger-page map blocks this finer mapping.
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }
        pte_ref.store(PTEntry::new_table(
            Arch::make_private_address(prepared.root_paddr()),
            parent_flags,
        ));
        prepared.release();
        Ok(true)
    }

    #[inline(always)]
    pub fn translate(&self, vaddr: VirtAddr) -> Result<Translation<Arch>, PagingError> {
        let snapshot = self.walk(vaddr);
        let level = snapshot.level();
        let entry = snapshot.read();
        // Keep the common 4 KiB translation path free of dynamic level-size dispatch.
        if level == PageLevel::Level0 {
            if !entry.present() {
                return Err(PagingError::NotMapped);
            }
            let offset = vaddr.bits() & (Self::SMALL.size() - 1);
            return Ok(Translation::new(
                PhysAddr::from((entry.paddr_field() & !(Self::SMALL.size() - 1)) + offset),
                level,
            ));
        }
        if !entry.is_present_leaf(level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (level.size() - 1);
        Ok(Translation::new(
            PhysAddr::from((entry.paddr_field() & !(level.size() - 1)) + offset),
            level,
        ))
    }

    #[inline(always)]
    pub fn phys_addr(&self, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        self.translate(vaddr).map(|frame| frame.address())
    }

    /// Checks self-mappings using atomic observations. Arch whole-tree result
    /// requires the caller to exclude concurrent content updates.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        self.tree.validate()
    }

    /// Inputs: typed range and flags.
    /// Requires: none.
    /// Returns: validation status.
    fn check_map_region<PS: PageSize>(
        &self,
        range: PageRangeInclusive<PS>,
        flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
        if target > PageLevel::Level2 || target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
        if range.is_empty() {
            return Err(PagingError::InvalidRange);
        }
        self.tree.policy().check_range(
            MaxLevel::LEVEL,
            range.start.start_address(),
            range.end.start_address(),
        )?;
        self.tree.policy().check_address(MaxLevel::LEVEL, range.end.start_address())
    }

    /// Inputs: frame, level, and flags.
    /// Requires: aligned frame.
    /// Returns: private leaf descriptor.
    fn leaf_entry(paddr: PhysAddr, target: PageLevel, flags: Arch::PTFlags) -> PTEntry<Arch> {
        let addr = Arch::make_private_address(paddr);
        let flags = Arch::filter_flags(flags);
        let flags = if target.is_leaf() { flags } else { flags.with(Arch::PTFlags::HUGE) };
        PTEntry::new(addr, flags)
    }

    /// Maps a run contained by one table page after confirming its slots are available.
    fn map_leaf_run<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>, L: WalkLevelImpl>(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc, L>,
        pages: PageRangeInclusive<PS>,
        frames: &mut I,
        flags: Arch::PTFlags,
        mapped_pages: &mut usize,
    ) -> Result<(), PagingError> {
        let target = page.level();
        debug_assert_eq!(target.size(), PS::SIZE);
        let start_index = pages.start.pt_index();
        let end_index = pages.end.pt_index();
        debug_assert!(start_index <= end_index);

        {
            let _guard = self.wperms.lock(page.paddr());
            for index in start_index..=end_index {
                let observed = page.load(index);
                if observed.is_present_table(target) {
                    return Err(PagingError::NotLeafEntry);
                }
                if observed.present() {
                    return Err(PagingError::EntryAlreadyPresent { level: target });
                }
            }
        }

        let run_len = end_index - start_index + 1;
        let mut buffered = [None; PT_ENTRY_COUNT];
        let mut count = 0;
        while count < run_len {
            let Some(frame) = frames.next() else {
                break;
            };
            buffered[count] = Some(frame);
            count += 1;
        }

        let _guard = self.wperms.lock(page.paddr());
        for index in start_index..start_index + count {
            let observed = page.load(index);
            if observed.is_present_table(target) {
                return Err(PagingError::NotLeafEntry);
            }
            if observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level: target });
            }
        }
        let mapped_4k_per_page = PS::SIZE / Regular::SIZE;
        for (offset, frame) in buffered[..count].iter().enumerate() {
            let frame = frame.expect("buffered frame");
            let index = start_index + offset;
            page.store(index, Self::leaf_entry(frame.start_address(), target, flags));
            *mapped_pages += mapped_4k_per_page;
        }
        if count == run_len {
            Ok(())
        } else {
            Err(PagingError::InvalidRange)
        }
    }

    /// Returns the existing child or publishes a newly prepared child into an absent slot.
    fn mapping_child<'tree, L: WalkLevelImpl>(
        &self,
        parent: &PTPagePointer<'tree, Arch, Alloc, L>,
        index: usize,
    ) -> Result<PTPagePointer<'tree, Arch, Alloc, L::ChildLevel>, PagingError> {
        let observed = parent.load(index);
        if observed.is_present_table(parent.level()) {
            return parent.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry);
        }
        if observed.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
        }

        let parent_flags = Arch::filter_flags(Arch::PTFlags::parent_flags());
        let prepared = PTPageTree::<Arch, Alloc, L::ChildLevel>::new_root(KernelPolicy)?;
        let _guard = self.wperms.lock(parent.paddr());
        let current = parent.load(index);
        if current.is_present_table(parent.level()) {
            return parent.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
        }
        let installed =
            PTEntry::new_table(Arch::make_private_address(prepared.root_paddr()), parent_flags);
        parent.store(index, installed);
        prepared.release();
        parent.child_from_observed(installed).map_err(|_| PagingError::NotLeafEntry)
    }

    /// Partitions the range by table entry and descends through statically typed child levels.
    #[inline(always)]
    fn do_map_region<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>, L: WalkLevelImpl>(
        &self,
        ptpage: &PTPagePointer<'_, Arch, Alloc, L>,
        range: PageRangeInclusive<PS>,
        frames: &mut I,
        flags: Arch::PTFlags,
        mapped_pages: &mut usize,
    ) -> Result<(), PagingError> {
        let level = L::LEVEL;
        if level.size() == PS::SIZE {
            return self.map_leaf_run(ptpage, range, frames, flags, mapped_pages);
        }
        if level.size() < PS::SIZE {
            return Err(PagingError::InvalidLevel);
        }
        let mut start = range.start;
        for _ in 0..PT_ENTRY_COUNT {
            let offset = (start.start_address().bits() & (level.size() - 1)) / PS::SIZE;
            let count = (level.size() / PS::SIZE - offset).min(range.end - start + 1);
            let end = start + count - 1;
            let index = entry_index(start.start_address(), level);
            let child = self.mapping_child(ptpage, index)?;
            self.do_map_region(
                &child,
                Page::range_inclusive(start, end),
                frames,
                flags,
                mapped_pages,
            )?;
            if end.start_address() == range.end.start_address() {
                return Ok(());
            }
            start = end + 1;
        }
        unreachable!("range spans more entries than one page-table page")
    }

    /// Traverses a validated range while retaining every installed table link.
    fn unmap_region_sweep(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        if start == end {
            return Ok(());
        }
        let root = self.root_view();
        let mut visitor = UnmapRegionVisitor { table: self, state };
        let high_start = VirtAddr::new(LOW_CANONICAL_END).bits();
        let mut visit = |first: usize, last: usize| match MaxLevel::visit_stable(
            root.duplicate(),
            None,
            first,
            last,
            &mut visitor,
        ) {
            ControlFlow::Continue(()) => Ok(()),
            ControlFlow::Break(error) => Err(error),
        };
        if start.bits() < LOW_CANONICAL_END && end.bits() >= high_start {
            visit(start.bits(), LOW_CANONICAL_END)?;
            visit(high_start, end.bits())
        } else {
            visit(start.bits(), end.bits())
        }
    }

    /// Maps `page` to the matching physical `frame`, building intermediate
    /// tables with `parent_flags`. Existing mappings are never overwritten.
    pub fn map_with_parent_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        self.do_map(page, frame, flags, shared, parent_flags)
    }

    /// [`Self::map_with_parent_flags`] with the architecture's default flags
    /// for intermediate tables.
    pub fn map<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
    ) -> Result<(), PagingError> {
        self.map_with_parent_flags(page, frame, flags, shared, Arch::PTFlags::parent_flags())
    }

    /// Removes exactly `page`.
    ///
    /// Inputs: a typed page and optional split invalidation scope. `None`
    /// forbids splitting; `Some(all_cpus)` permits it.
    ///
    /// Requires: `PS` must be a supported leaf level within this table, and the
    /// ownership policy must permit the page address.
    ///
    /// Returns: the removed entry, if mapped, and any remaining flush obligation.
    /// Returns [`PagingError::WrongPageSize`] when the existing mapping has a
    /// different leaf size and cannot or may not be split to `PS`.
    #[inline(always)]
    pub fn unmap<PS: PageSize>(
        &self,
        page: Page<PS>,
        split_all_cpus: Option<bool>,
    ) -> UnmapEntryResult<Arch> {
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        self.unmap_from(&self.root_view(), page, split_all_cpus)
    }

    /// Removes `page` below a previously validated pinned subtree.
    #[inline(always)]
    fn unmap_from<PS: PageSize, L: WalkLevelImpl + LeafSplitLevelImpl>(
        &self,
        table: &PTPagePointer<'_, Arch, Alloc, L>,
        page: Page<PS>,
        split_all_cpus: Option<bool>,
    ) -> UnmapEntryResult<Arch> {
        let vaddr = page.start_address();
        if L::LEVEL < PS::LEVEL {
            return Err(PagingError::WrongPageSize);
        }
        let index = entry_index(vaddr, L::LEVEL);
        let observed = table.load(index);
        if observed.is_present_table(L::LEVEL) {
            let child =
                table.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
            return self.unmap_from(&child, page, split_all_cpus);
        }

        let guard = self.wperms.lock(table.paddr());
        let pte_ref = table.entry(index);
        let entry = pte_ref.load();
        if entry.is_present_table(L::LEVEL) {
            let child = table.child_from_observed(entry).map_err(|_| PagingError::NotLeafEntry)?;
            drop(guard);
            return self.unmap_from(&child, page, split_all_cpus);
        }
        if !entry.present() {
            return Ok((None, MayNeedFlush::none()));
        }
        if L::LEVEL == PS::LEVEL {
            let entry = pte_ref.swap(PTEntry::empty());
            return Ok((Some(entry), PTPage::<Arch, Alloc>::flush_for_leaf(vaddr, PS::LEVEL)));
        }

        let all_cpus = split_all_cpus.ok_or(PagingError::WrongPageSize)?;
        // SAFETY: the content guard pins the entry and excludes competing writers.
        let flush = unsafe { L::split_leaf_to::<Arch, Alloc, PS>(pte_ref, page, all_cpus) }?;
        let child_entry = table.load(index);
        let child =
            table.child_from_observed(child_entry).map_err(|_| PagingError::NotLeafEntry)?;
        drop(guard);
        let (entry, pending) = self.unmap_from(&child, page, None)?;
        Ok((entry, flush.and(pending)))
    }

    /// Splits the huge leaf represented by `page` one level while preserving
    /// its mappings. New pages are prepared privately; the content guard covers
    /// publication and flushing.
    /// `all_cpus = false` requires no affected translations on other CPUs and
    /// no migration during the operation.
    pub fn split(
        &self,
        page: Page<Huge>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        let mapping = self.root_view().walk(vaddr);
        if mapping.level() != Huge::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        let _guard = self.wperms.lock(mapping.page_paddr());
        // SAFETY: the content guard pins the entry and excludes software writers.
        match unsafe { PTPage::<Arch, Alloc>::split_leaf::<Huge>(mapping.entry(), vaddr, all_cpus) }
        {
            Err(PagingError::NotLeafEntry) => Err(PagingError::InvalidLevel),
            result => result,
        }
    }

    /// Replaces flags for exactly one typed page, splitting
    /// a larger leaf if needed. Frame, tags, PAT and Arch/D history are retained.
    /// Arch finer subtree is reported rather than overwritten.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    #[inline(always)]
    pub fn set_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
        self.update_flags(page, Arch::filter_flags(flags), all_cpus)
    }

    #[inline(always)]
    /// Inputs: page, flags, and flush scope.
    /// Requires: present flags.
    /// Returns: flush obligation.
    fn set_flags_4k(
        &self,
        page: Page<Regular>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let vaddr = page.start_address();
        let mapping = self.root_view().walk(vaddr);
        if mapping.level() != Self::SMALL {
            return self.with_locked_leaf(page, |entry, level| unsafe {
                PTPage::<Arch, Alloc>::update_leaf_flags_at(entry, level, page, flags, all_cpus)
            });
        }

        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        let current = mapping.entry().load();
        if !current.is_present_leaf(Self::SMALL) {
            return Err(PagingError::NotMapped);
        }
        // SAFETY: the pte_ref is pinned at Level0 and the content guard excludes writers.
        Ok(unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_in_place(
                mapping.entry(),
                current,
                Self::SMALL,
                vaddr,
                flags,
            )
        })
    }

    /// Replaces flags across a page-aligned range with per-entry effects, not a transaction.
    /// On error, the returned obligation covers any unflushed prefix edits.
    /// Each table page is locked only while its affected entries are updated.
    /// `all_cpus` selects its scope as in [`Self::split`].
    pub fn set_flags_range(
        &self,
        start: VirtAddr,
        end: VirtAddr,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<Arch::TlbFlushTok>) {
        let flush = MayNeedFlush::none();
        if let Err(error) = self.tree.policy().check_range(MaxLevel::LEVEL, start, end) {
            return (Err(error), flush);
        }
        if start > end
            || !start.is_aligned(Self::SMALL.size())
            || !end.is_aligned(Self::SMALL.size())
        {
            return (Err(PagingError::InvalidRange), flush);
        }
        if !flags.present() {
            return (Err(PagingError::InvalidFlags), flush);
        }
        if start == end {
            return (Ok(()), flush);
        }
        self.set_flags_range_inner(start.bits(), end.bits(), Arch::filter_flags(flags), all_cpus)
    }

    /// Inputs: validated bounds and flags.
    /// Requires: nonempty range.
    /// Returns: result and flush.
    fn set_flags_range_inner(
        &self,
        start: usize,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<Arch::TlbFlushTok>) {
        let mut state = RangeFlagsState {
            cursor: start,
            flush: MayNeedFlush::none(),
            footprint: FlushFootprint::default(),
            descents_left: MaxLevel::LEVEL.depth(),
            descent_cursor: start,
            partial_leaves_left: 2,
        };
        loop {
            if let Some(result) = self.set_flags_range_step(end, flags, all_cpus, &mut state) {
                return result;
            }
        }
    }

    /// Inputs: range end, flags, and state.
    /// Requires: live cursor.
    /// Returns: completion if finished.
    fn set_flags_range_step(
        &self,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
        state: &mut RangeFlagsState<Arch::TlbFlushTok>,
    ) -> Option<RangeFlagsResult<Arch::TlbFlushTok>> {
        if state.cursor != state.descent_cursor {
            state.descent_cursor = state.cursor;
            state.descents_left = MaxLevel::LEVEL.depth();
        }
        let mapping = self.root_view().walk(VirtAddr::from(state.cursor));
        if let WalkPosition::Level0(position) = &mapping {
            return match self.set_flags_l0_run(
                &position.page,
                mapping.page_paddr(),
                position.index,
                end,
                flags,
                state,
            ) {
                Ok(cursor) if cursor == end => Some(state.finish(Ok(()))),
                Ok(cursor) => {
                    state.cursor = cursor;
                    None
                }
                Err(error) => Some(state.finish(Err(error))),
            };
        }

        let mut locked_page = None;
        let mut guard: Option<WP::Guard<'_>> = None;
        let root = self.root_view();
        let result = PTPage::<Arch, Alloc>::sweep_range(
            &root,
            VirtAddr::from(state.cursor),
            VirtAddr::from(end),
            &mut |page, mapping, entry_start, entry_end| {
                let Mapping { pte_value: observed, pte_ref, level } = mapping;
                let current = if locked_page != Some(page) {
                    guard = None;
                    guard = Some(self.wperms.lock(page));
                    locked_page = Some(page);
                    pte_ref.load()
                } else {
                    observed
                };
                if current.is_present_table(level) {
                    return Err(RangeUpdateError::Descend);
                }
                if !current.is_present_leaf(level) {
                    return Err(RangeUpdateError::Paging(PagingError::NotMapped));
                }
                let leaf_start = entry_start & !(level.size() - 1);
                if entry_start != leaf_start {
                    return Err(RangeUpdateError::Split(
                        entry_start,
                        Self::largest_covered_level(entry_start, entry_end, level, false),
                    ));
                }
                if entry_end != leaf_start.saturating_add(level.size()) {
                    let target = Self::largest_covered_level(entry_start, entry_end, level, true);
                    return Err(RangeUpdateError::Split(entry_end - target.size(), target));
                }
                let mut desired = current;
                PTPage::<Arch, Alloc>::set_leaf_flags(&mut desired, flags);
                if desired.raw() != current.raw() {
                    pte_ref.update_valid_entry(current, desired);
                    state.footprint.include(VirtAddr::from(entry_start), level);
                }
                Ok(())
            },
        );
        drop(guard);
        match result {
            Ok(_) => Some(state.finish(Ok(()))),
            Err((retry, RangeUpdateError::Descend)) => {
                if state.descents_left == 0 {
                    unreachable!("page-table range update exceeded its descent bound");
                }
                state.descents_left -= 1;
                state.cursor = retry.bits();
                None
            }
            Err((retry, RangeUpdateError::Split(split_address, target))) => {
                if state.partial_leaves_left == 0 {
                    unreachable!("page-table range update exceeded its partial-leaf bound");
                }
                state.partial_leaves_left -= 1;
                let split_address = VirtAddr::from(split_address);
                let update = match target {
                    PageLevel::Level0 => self.update_flags(
                        Page::<Regular>::containing_address(split_address),
                        flags,
                        all_cpus,
                    ),
                    PageLevel::Level1 => self.update_flags(
                        Page::<Huge>::containing_address(split_address),
                        flags,
                        all_cpus,
                    ),
                    PageLevel::Level2 => self.update_flags(
                        Page::<SizeLevel2>::containing_address(split_address),
                        flags,
                        all_cpus,
                    ),
                    _ => Err(PagingError::InvalidLevel),
                };
                match update {
                    Ok(pending) => {
                        let flush = core::mem::replace(&mut state.flush, MayNeedFlush::none());
                        state.flush = flush.and(pending);
                        state.cursor = retry.bits();
                        None
                    }
                    Err(error) => Some(state.finish(Err(error))),
                }
            }
            Err((_, RangeUpdateError::Paging(error))) => Some(state.finish(Err(error))),
        }
    }

    /// Inputs: L0 run and state.
    /// Requires: matching table.
    /// Returns: next cursor or error.
    fn set_flags_l0_run(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc, Lvl<0>>,
        page_paddr: PhysAddr,
        start_index: usize,
        end: usize,
        flags: Arch::PTFlags,
        state: &mut RangeFlagsState<Arch::TlbFlushTok>,
    ) -> Result<usize, PagingError> {
        let _guard = self.wperms.lock(page_paddr);
        let start = state.cursor;
        let count = ((end - start) / Self::SMALL.size()).min(PT_ENTRY_COUNT - start_index);
        let mut changed = false;
        for index in start_index..start_index + count {
            let pte_ref = page.entry(index);
            let current = pte_ref.load();
            if !current.is_present_leaf(Self::SMALL) {
                let run_end = start + (index - start_index) * Self::SMALL.size();
                Self::include_l0_footprint(&mut state.footprint, changed, start, run_end);
                return Err(PagingError::NotMapped);
            }
            let mut desired = current;
            PTPage::<Arch, Alloc>::set_leaf_flags(&mut desired, flags);
            if desired.raw() != current.raw() {
                pte_ref.update_valid_entry(current, desired);
                changed = true;
            }
        }
        let run_end = start + count * Self::SMALL.size();
        Self::include_l0_footprint(&mut state.footprint, changed, start, run_end);
        Ok(VirtAddr::from(run_end).bits())
    }

    /// Inputs: footprint and run bounds.
    /// Requires: nonempty changed run.
    /// Returns: nothing.
    fn include_l0_footprint(
        footprint: &mut FlushFootprint,
        changed: bool,
        start: usize,
        end: usize,
    ) {
        if changed {
            footprint.include(VirtAddr::from(start), Self::SMALL);
            footprint.include(VirtAddr::from(end - Self::SMALL.size()), Self::SMALL);
        }
    }

    /// Inputs: bounds and maximum level.
    /// Requires: nonempty range.
    /// Returns: largest covered level.
    fn largest_covered_level(
        start: usize,
        end: usize,
        level: PageLevel,
        align_end: bool,
    ) -> PageLevel {
        let mut target = level.child().unwrap();
        while target > Self::SMALL && !Self::level_fits_range(start, end, target, align_end) {
            target = target.child().unwrap();
        }
        target
    }

    /// Inputs: bounds, level, and alignment side.
    /// Requires: ordered bounds.
    /// Returns: fit decision.
    fn level_fits_range(start: usize, end: usize, level: PageLevel, align_end: bool) -> bool {
        if end - start < level.size() {
            return false;
        }
        let boundary = if align_end { end } else { start };
        boundary & (level.size() - 1) == 0
    }

    /// Retags `page` as shared, splitting if needed.
    /// Discharge the returned flush unless BBM completes it synchronously.
    /// `all_cpus` selects the scope only when the architecture requires BBM.
    pub fn set_shared<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.with_locked_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_encryption_leaf(entry, level, page, true, all_cpus)
        })
    }

    /// Retags `page` as private.
    /// Discharge the returned flush unless BBM completes it synchronously.
    /// `all_cpus` selects the scope only when the architecture requires BBM.
    pub fn set_private<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.with_locked_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_encryption_leaf(entry, level, page, false, all_cpus)
        })
    }

    #[inline(always)]
    /// Inputs: page, flags, and flush scope.
    /// Requires: present flags.
    /// Returns: flush obligation.
    fn update_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        if target == Self::SMALL {
            self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
            return self.set_flags_4k(Page::containing_address(vaddr), flags, all_cpus);
        }
        self.with_locked_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_at(entry, level, page, flags, all_cpus)
        })
    }

    /// Inputs: page and update callback.
    /// Requires: policy-approved address.
    /// Returns: callback result.
    fn with_locked_leaf<PS: PageSize>(
        &self,
        page: Page<PS>,
        update: impl FnOnce(
            PTEntryRef<'_, Arch>,
            PageLevel,
        ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError>,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > PageLevel::Level2 || target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.level() < target {
                return Err(PagingError::NotLeafEntry);
            }
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            if mapping.entry().load().is_present_table(mapping.level()) {
                continue;
            }
            return update(mapping.entry(), mapping.level());
        }
        unreachable!("page-table update exceeded the tree depth")
    }

    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        let view = self.root_view();
        let entry = view.load(idx);
        entry.is_present_table(view.level()).then(|| PhysAddr::from(entry.address()))
    }

    /// Maps each page in `range` to the next frame. A failure retains the
    /// mapped prefix and reports the remaining number of 4 KiB pages.
    /// Overlapping writers can change which prefix wins.
    /// Iterator callbacks run without a content guard; a racing writer can
    /// therefore consume frames from a leaf run that loses publication.
    pub fn map_region<PS: PageSize>(
        &self,
        range: PageRangeInclusive<PS>,
        frames: &mut impl Iterator<Item = PhysFrame<PS>>,
        flags: Arch::PTFlags,
    ) -> Result<(), MapRegionError> {
        let unmapped_pages = range.len() * PS::SIZE / Regular::SIZE;
        self.check_map_region(range, flags)
            .map_err(|error| MapRegionError { error, unmapped_pages })?;
        let mut mapped_pages = 0;
        let root = self.root_view();
        self.do_map_region(&root, range, frames, flags, &mut mapped_pages).map_err(|error| {
            MapRegionError { error, unmapped_pages: unmapped_pages - mapped_pages }
        })
    }

    /// Maps adjacent fixed-size 2 MiB and 4 KiB ranges in virtual-address order.
    /// A failure retains the mapped prefix across both ranges.
    pub fn map_region_mixed(
        &self,
        range_2m: PageRangeInclusive<Huge>,
        frames_2m: &mut impl Iterator<Item = PhysFrame<Huge>>,
        range_4k: PageRangeInclusive<Regular>,
        frames_4k: &mut impl Iterator<Item = PhysFrame<Regular>>,
        flags: Arch::PTFlags,
    ) -> Result<(), MapRegionError> {
        /// Inputs: two ranges.
        /// Requires: nonempty ranges.
        /// Returns: canonical adjacency decision.
        fn followed_by<A: PageSize, B: PageSize>(
            first: PageRangeInclusive<A>,
            second: PageRangeInclusive<B>,
        ) -> bool {
            first.end.start_address().bits() <= usize::MAX - A::SIZE
                && (first.end + 1).start_address() == second.start.start_address()
        }

        let pages_2m = range_2m.len() * Huge::SIZE / Regular::SIZE;
        let pages_4k = range_4k.len();
        if range_2m.is_empty()
            || range_4k.is_empty()
            || !(followed_by(range_2m, range_4k) || followed_by(range_4k, range_2m))
        {
            return Err(MapRegionError {
                error: PagingError::InvalidRange,
                unmapped_pages: pages_2m + pages_4k,
            });
        }

        if range_2m.start.start_address() < range_4k.start.start_address() {
            self.map_region(range_2m, frames_2m, flags).map_err(|failure| MapRegionError {
                error: failure.error,
                unmapped_pages: failure.unmapped_pages + pages_4k,
            })?;
            self.map_region(range_4k, frames_4k, flags)
        } else {
            self.map_region(range_4k, frames_4k, flags).map_err(|failure| MapRegionError {
                error: failure.error,
                unmapped_pages: failure.unmapped_pages + pages_2m,
            })?;
            self.map_region(range_2m, frames_2m, flags)
        }
    }

    /// Unmaps `[start, end)` at the largest currently represented leaf sizes.
    /// Partially covered huge leaves are split only as far as the range needs.
    /// Splitting can allocate; an error leaves the successfully processed
    /// prefix unmapped and synchronously flushes it.
    /// Reports whether every smallest page in the range was mapped.
    pub fn unmap_region(
        &self,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(bool, MayNeedFlush<Arch::TlbFlushTok>), PagingError> {
        self.tree.policy().check_range(MaxLevel::LEVEL, start, end)?;
        let mut all_mapped = true;
        let mut footprint = FlushFootprint::default();
        let mut state = RangeUnmapState { all_mapped: &mut all_mapped, footprint: &mut footprint };
        if let Err(error) = self.unmap_region_sweep(start, end, &mut state) {
            let flush = footprint.token::<Arch::TlbFlushTok>();
            if flush.is_pending() {
                flush.flush_tlb_global_sync();
            }
            return Err(error);
        }
        Ok((all_mapped, footprint.token::<Arch::TlbFlushTok>()))
    }

    /// Frees empty tables on one path, never the root.
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_addr(&mut self, vaddr: VirtAddr) -> usize {
        if !self.tree.policy().owns_top_entry(entry_index(vaddr, MaxLevel::LEVEL)) {
            return 0;
        }
        // SAFETY: borrowing excludes local walkers; the caller supplies
        // exclusive ownership and hardware exclusion.
        // Arch zero word excludes non-present state retained by concurrent protocols.
        unsafe { reclaim_path(&self.root_view(), vaddr, |entry| entry.is_clear()) }
    }

    /// Frees empty tables intersecting the half-open range, never the root.
    /// # Safety
    /// As in [`Self::free_page_table_by_addr`], for the entire affected subtree.
    pub unsafe fn free_page_table_by_range(&mut self, start: VirtAddr, end: VirtAddr) {
        assert!(start <= end);
        if start < end {
            let span = MaxLevel::LEVEL.size() * PT_ENTRY_COUNT;
            let first = start.bits() & (span - 1);
            let last = ((end.bits() - 1) & (span - 1)) + 1;
            assert!(first < last, "range wraps the root's address space");
            // SAFETY: the caller supplies exclusive ownership and excludes all walkers.
            unsafe {
                reclaim_range(
                    &self.root_view(),
                    first,
                    last,
                    |index| self.tree.policy().owns_top_entry(index),
                    // Arch zero word excludes non-present state retained by concurrent protocols.
                    |entry| entry.is_clear(),
                )
            };
        }
    }

    /// Frees owned subtrees, retaining borrowed root entries and all data frames.
    /// # Safety
    /// Every owned child table must come from this allocator, with no other parent
    /// links. Exclude all other walkers and invalidate cached table pointers
    /// before reusing pages or resuming hardware walks.
    pub unsafe fn free_children(&mut self) {
        // SAFETY: the caller supplies ownership and quiescence for every selected subtree.
        unsafe { self.root_view().free_children(|index| self.tree.policy().owns_top_entry(index)) };
    }
}

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
{
    /// Installs an owned subtree in an absent root entry.
    /// # Safety
    /// The subtree must be initialized, correctly leveled, acyclic, mapped and
    /// allocated by this controller's allocator. Installation transfers
    /// ownership; no other parent may link to it.
    pub unsafe fn populate(
        &mut self,
        idx: usize,
        subpage_pa: PhysAddr,
    ) -> Result<bool, PagingError> {
        if MaxLevel::LEVEL.is_leaf() {
            return Err(PagingError::InvalidLevel);
        }
        let desired = PTEntry::new_table(
            Arch::make_private_address(subpage_pa),
            Arch::PTFlags::parent_flags(),
        );
        let pte_ref = self.root_view().entry(idx);
        let _guard = self.wperms.lock(self.tree.root_paddr());
        let entry = pte_ref.load();
        if entry.is_present_table(MaxLevel::LEVEL) && entry.address() == subpage_pa.bits() {
            return Ok(false);
        }
        if entry.is_present_table(MaxLevel::LEVEL) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level: MaxLevel::LEVEL });
        }
        pte_ref.store(desired);
        Ok(true)
    }
}
