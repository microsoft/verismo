//! The `pagetable` API with concurrent walks and serialized entry updates.
//! Shared borrows pin table pages; exclusive borrows permit reclamation.
//! An external RwLock can provide those borrows. It does not fence hardware
//! walkers: the embedder supplies synchronous TLB hooks and hardware quiescence.
#![doc = include_str!("../concurrency.md")]

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::mapping::UnmapEntryResult;
use crate::structs::os_contract::{
    DirectMappedAllocator, MapRegionError, PagingAllocator, PagingError,
};
use crate::structs::page::{Page, PageRangeInclusive};
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy, UserPolicy};
use crate::structs::ptpage::{
    free_children, reclaim_path, reclaim_range, FlushFootprint, PTPage, PTPagePointer, PTPageTree,
    Translation, WalkResult,
};
use crate::structs::sizes::{
    entry_index, next_boundary, page_level_for_size, PageSize, Size1GiB, Size2MiB, Size4KiB,
    PT_ENTRY_COUNT,
};
use crate::structs::tlb::{MayNeedFlush, TlbFlush};

#[derive(Default)]
struct RangeMapState {
    mapped_pages: usize,
}

struct RangeUnmapState<'a> {
    all_mapped: &'a mut bool,
    footprint: &'a mut FlushFootprint,
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

impl<T: TlbFlush> RangeFlagsState<T> {
    /// Inputs: final result; Requires: completed updates; Returns: result with accumulated flush.
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

    /// Inputs: table address; Requires: stable lock domain; Returns: exclusive write guard.
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
    MaxLevel: LevelSpec,
    WP,
    T = (),
    Owned: PagingOwnershipPolicy = KernelPolicy,
> {
    tree: PTPageTree<Arch, Alloc, MaxLevel, Owned>,
    wperms: WP,
    marker: PhantomData<T>,
}

/// Arch concurrent kernel page table using `WP` as its PTE write-permission domain.
pub type KernelPageTable<Arch, Alloc, MaxLevel, WP, T = ()> =
    PageTable<Arch, Alloc, MaxLevel, WP, T, KernelPolicy>;
/// Arch concurrent user page table borrowing the configured kernel root entries.
pub type UserPageTable<
    'kernel,
    Arch,
    Alloc,
    MaxLevel,
    WP,
    const START: usize,
    const END: usize,
    T = (),
> = PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<'kernel, START, END>>;

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: DirectMappedAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
{
    /// Direct-maps the allocator's region with ordinary memory accesses:
    /// construction has no concurrent readers and takes no content locks.
    pub fn new(wperms: WP, flags: Arch::PTFlags) -> Result<Self, PagingError> {
        let root_pa = PTPage::<Arch, Alloc>::new_direct_mapped(MaxLevel::LEVEL, flags)?;
        // SAFETY: construction produced a validated, exclusively owned, unpublished tree.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree, wperms, marker: PhantomData })
    }
}

impl<Arch, Alloc, MaxLevel, WP, T> PageTable<Arch, Alloc, MaxLevel, WP, T>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
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
        unsafe {
            PTPage::<Arch, Alloc>::validate_tree(root_pa, MaxLevel::LEVEL, |pte_ref| {
                PTEntryRef::from_raw(pte_ref.cast_mut()).load()
            })
        }?;
        // SAFETY: validation establishes shape; ownership and quiescence are the caller's duty.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree, wperms, marker: PhantomData })
    }

    /// Borrows existing subtrees at `START..END`; the entire range becomes immutable.
    /// Initialize shared root entries before copying if later growth must be visible.
    /// # Safety
    /// `Alloc` must resolve shared physical addresses to the same table pages as `other`.
    /// Shared pages must outlive both trees at identical virtual prefixes,
    /// use the same content-lock domain, and not be reclaimed while in use.
    pub unsafe fn new_from_sharing_top<'kernel, const START: usize, const END: usize>(
        wperms: WP,
        other: &'kernel Self,
    ) -> Result<UserPageTable<'kernel, Arch, Alloc, MaxLevel, WP, START, END, T>, PagingError> {
        let policy = UserPolicy::<START, END>::new();
        let mut tree = PTPageTree::new_root(policy)?;
        {
            // SAFETY: the fresh destination has no software or hardware users.
            let page = unsafe { tree.page_mut() };
            for idx in START..END {
                let entry = other.root_view().load(idx);
                if entry.is_table(MaxLevel::LEVEL) {
                    *page.entry_mut(idx) = entry;
                }
            }
        }
        let this = PageTable { tree, wperms, marker: PhantomData };
        this.validate_page_table()?;
        Ok(this)
    }

    /// Gives up the tree and returns its root and content-lock domain.
    /// Arch borrowed root remains borrowed; its ownership is not transferred.
    pub fn leak(self) -> (WP, PhysAddr) {
        let (wperms, _, root_pa) = self.leak_parts();
        (wperms, root_pa)
    }

    /// Installs an owned subtree in an absent root entry.
    /// # Safety
    /// The subtree must be initialized, correctly leveled, acyclic, mapped and
    /// allocated by this controller's allocator.
    /// Arch new installation transfers its ownership; no other parent may link to it.
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
        if entry.is_table(MaxLevel::LEVEL) && entry.address() == subpage_pa.bits() {
            return Ok(false);
        }
        if entry.is_table(MaxLevel::LEVEL) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level: MaxLevel::LEVEL });
        }
        // Only an absent entry changes; ownership transfers with publication.
        pte_ref.store(desired);
        Ok(true)
    }
}

impl<'kernel, Arch, Alloc, MaxLevel, WP, T, const START: usize, const END: usize>
    PageTable<Arch, Alloc, MaxLevel, WP, T, UserPolicy<'kernel, START, END>>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak(self) -> (WP, UserPolicy<'kernel, START, END>, PhysAddr) {
        self.leak_parts()
    }
}

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    WP: LockSpec<T>,
    Owned: PagingOwnershipPolicy,
{
    const SMALL: PageLevel = PageLevel::Level0;

    /// Inputs: owned controller; Requires: none; Returns: lock, policy, and unreclaimed root.
    fn leak_parts(self) -> (WP, Owned, PhysAddr) {
        let (policy, root_pa) = self.tree.into_parts();
        (self.wperms, policy, root_pa)
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    /// Inputs: controller borrow; Requires: live tree; Returns: pinned atomic root view.
    fn root_view(&self) -> PTPagePointer<'_, Arch, Alloc> {
        self.tree.root()
    }

    /// Arch leaf/absent-entry snapshot. It holds no content lock and gives no
    /// authority to dereference or free the translated data frame.
    #[inline(always)]
    pub fn walk(&self, vaddr: VirtAddr) -> WalkResult<Arch> {
        let position = self.tree.root().walk(vaddr);
        WalkResult::new(position.observed, position.page.level())
    }

    /// Inputs: page, frame, and flags; Requires: valid typed mapping; Returns: mapping status.
    #[inline(always)]
    fn do_map<PS: PageSize>(
        &self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        let paddr = frame.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
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
            let level = mapping.page.level();
            if level < target {
                return Err(PagingError::NotLeafEntry);
            }
            if level == target {
                return self.install_leaf(&mapping.page, mapping.index, leaf);
            }
            if mapping.observed.is_table(level) {
                mapping = mapping.page.walk(vaddr);
                continue;
            }
            if mapping.observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level });
            }
            if self.alloc_and_install_leaf(
                &mapping.page,
                mapping.index,
                page,
                parent_flags,
                leaf,
            )? {
                return Ok(());
            }
            mapping = mapping.page.walk(vaddr);
        }
        unreachable!("mapping traversal exceeded the page-table depth")
    }

    /// Inputs: page, index, and leaf; Requires: live table; Returns: leaf installation status.
    fn install_leaf(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc>,
        index: usize,
        leaf: PTEntry<Arch>,
    ) -> Result<(), PagingError> {
        let level = page.level();
        let _guard = self.wperms.lock(page.paddr());
        let pte_ref = page.entry(index);
        let entry = pte_ref.load();
        if entry.is_table(level) {
            return Err(PagingError::NotLeafEntry);
        }
        if entry.present() {
            return Err(PagingError::EntryAlreadyPresent { level });
        }
        pte_ref.store(leaf);
        Ok(())
    }

    /// Inputs: parent slot and leaf; Requires: absent path; Returns: whether this path was installed.
    fn alloc_and_install_leaf<PS: PageSize>(
        &self,
        parent: &PTPagePointer<'_, Arch, Alloc>,
        index: usize,
        page: Page<PS>,
        parent_flags: Arch::PTFlags,
        leaf: PTEntry<Arch>,
    ) -> Result<bool, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        let child_level = parent.level().child().unwrap();
        let mut prepared = PTPageTree::<Arch, Alloc>::new(child_level)?;
        prepared.grow(page, parent_flags)?;
        let prepared_mapping = prepared.root().walk(vaddr);
        debug_assert_eq!(prepared_mapping.page.level(), target);
        prepared_mapping.entry().store(leaf);

        let _guard = self.wperms.lock(parent.paddr());
        let pte_ref = parent.entry(index);
        let current = pte_ref.load();
        if current.is_table(parent.level()) {
            return Ok(false);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
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
        if !entry.is_leaf(level) {
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
        // SAFETY: this borrow pins every followed table; all observations are atomic.
        unsafe {
            PTPage::<Arch, Alloc>::validate_tree(
                self.tree.root_paddr(),
                MaxLevel::LEVEL,
                |pte_ref| PTEntryRef::from_raw(pte_ref.cast_mut()).load(),
            )
        }
    }

    /// Inputs: typed range and flags; Requires: none; Returns: validation status.
    fn check_map_region<PS: PageSize>(
        &self,
        range: PageRangeInclusive<PS>,
        flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        if target > MaxLevel::LEVEL {
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

    /// Inputs: frame, level, and flags; Requires: aligned frame; Returns: private leaf descriptor.
    fn leaf_entry(paddr: PhysAddr, target: PageLevel, flags: Arch::PTFlags) -> PTEntry<Arch> {
        let addr = Arch::make_private_address(paddr);
        let flags = Arch::filter_flags(flags);
        let flags = if target.is_leaf() { flags } else { flags.with(Arch::PTFlags::HUGE) };
        PTEntry::new(addr, flags)
    }

    /// Inputs: leaf run and frames; Requires: one matching leaf table; Returns: mapping status.
    fn map_leaf_run<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>>(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc>,
        pages: PageRangeInclusive<PS>,
        frames: &mut I,
        flags: Arch::PTFlags,
        state: &mut RangeMapState,
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
                if observed.is_table(target) {
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
            if observed.is_table(target) {
                return Err(PagingError::NotLeafEntry);
            }
            if observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level: target });
            }
        }
        let mapped_pages = PS::SIZE / Size4KiB::SIZE;
        for (offset, frame) in buffered[..count].iter().enumerate() {
            let frame = frame.expect("buffered frame");
            let index = start_index + offset;
            page.store(index, Self::leaf_entry(frame.start_address(), target, flags));
            state.mapped_pages += mapped_pages;
        }
        if count == run_len {
            Ok(())
        } else {
            Err(PagingError::InvalidRange)
        }
    }

    /// Inputs: parent slot and target page; Requires: non-leaf parent; Returns: resolved child.
    fn mapping_child<'tree>(
        &self,
        parent: &PTPagePointer<'tree, Arch, Alloc>,
        index: usize,
    ) -> Result<PTPagePointer<'tree, Arch, Alloc>, PagingError> {
        let observed = parent.load(index);
        if observed.is_table(parent.level()) {
            return parent.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry);
        }
        if observed.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
        }

        let child_level = parent.level().child().ok_or(PagingError::InvalidLevel)?;
        let parent_flags = Arch::filter_flags(Arch::PTFlags::parent_flags());
        let prepared = PTPageTree::<Arch, Alloc>::new(child_level)?;
        let _guard = self.wperms.lock(parent.paddr());
        let current = parent.load(index);
        if current.is_table(parent.level()) {
            return parent.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
        }
        parent.store(
            index,
            PTEntry::new_table(Arch::make_private_address(prepared.root_paddr()), parent_flags),
        );
        prepared.release();
        parent.child(index).map_err(|_| PagingError::NotLeafEntry)
    }

    #[inline(always)]
    /// Inputs: root, range, and frames; Requires: validated range; Returns: mapping status.
    fn do_map_region<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>>(
        &self,
        ptpage: &PTPagePointer<'_, Arch, Alloc>,
        range: PageRangeInclusive<PS>,
        frames: &mut I,
        flags: Arch::PTFlags,
        state: &mut RangeMapState,
    ) -> Result<(), PagingError> {
        let level = ptpage.level();
        if level.size() == PS::SIZE {
            return self.map_leaf_run(ptpage, range, frames, flags, state);
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
            self.do_map_region(&child, Page::range_inclusive(start, end), frames, flags, state)?;
            if end.start_address() == range.end.start_address() {
                return Ok(());
            }
            start = end + 1;
        }
        unreachable!("range spans more entries than one page-table page")
    }

    #[inline(always)]
    /// Inputs: L0 table and range; Requires: range intersects table; Returns: unmap status.
    fn unmap_region_l0(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        debug_assert_eq!(page.level(), PageLevel::Level0);
        let pages = Page::<Size4KiB>::range_inclusive(
            Page::containing_address(start),
            Page::containing_address(end - 1),
        );
        let mut index = entry_index(start, PageLevel::Level0);
        let mut first_changed = None;
        let mut last_changed = start;
        let _guard = self.wperms.lock(page.paddr());
        for leaf in pages {
            let vaddr = leaf.start_address();
            let pte_ref = page.entry(index);
            if pte_ref.load().is_leaf(PageLevel::Level0) {
                pte_ref.swap(PTEntry::empty());
                first_changed.get_or_insert(vaddr);
                last_changed = vaddr;
            } else {
                *state.all_mapped = false;
            }
            index = (index + 1) & (PT_ENTRY_COUNT - 1);
        }
        if let Some(first) = first_changed {
            state.footprint.include(first, PageLevel::Level0);
            state.footprint.include(last_changed, PageLevel::Level0);
        }
        Ok(())
    }

    #[inline(always)]
    /// Inputs: child table and range; Requires: matching level type; Returns: unmap status.
    fn unmap_region_child<PL: InnerLevel>(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        match PL::DEPTH {
            1 => self.unmap_region_l0(page, start, end, state),
            2 => self.unmap_region_level::<Lvl<1>>(page, start, end, state),
            3 => self.unmap_region_level::<Lvl<2>>(page, start, end, state),
            4 => self.unmap_region_level::<Lvl<3>>(page, start, end, state),
            _ => unreachable!("leaf page has no child"),
        }
    }

    #[inline(always)]
    /// Inputs: inner table and range; Requires: matching level type; Returns: unmap status.
    fn unmap_region_level<PL: InnerLevel>(
        &self,
        page: PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        let level = PL::LEVEL;
        debug_assert_eq!(page.level(), level);
        let page_paddr = page.paddr();
        while start < end {
            let entry_end = next_boundary(start, level, end);
            let index = entry_index(start, level);
            let pte_ref = page.entry(index);
            let mut observed = pte_ref.load();
            if observed.is_table(level) {
                let child =
                    page.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
                self.unmap_region_child::<PL>(child, start, entry_end, state)?;
                start = entry_end;
                continue;
            }
            let guard = self.wperms.lock(page_paddr);
            observed = pte_ref.load();
            if observed.is_table(level) {
                let child =
                    page.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
                drop(guard);
                self.unmap_region_child::<PL>(child, start, entry_end, state)?;
                start = entry_end;
                continue;
            }
            if !observed.is_leaf(level) {
                drop(guard);
                *state.all_mapped = false;
                start = entry_end;
                continue;
            }
            if start.is_aligned(level.size()) && end - start >= level.size() {
                pte_ref.swap(PTEntry::empty());
                drop(guard);
                state.footprint.include(start, level);
                start = entry_end;
                continue;
            }

            // SAFETY: the content guard pins the pte_ref and excludes competing writers.
            let _ = match level.child().unwrap() {
                PageLevel::Level0 => unsafe {
                    PTPage::<Arch, Alloc>::split_leaf(
                        pte_ref,
                        level,
                        Page::<Size4KiB>::containing_address(start),
                        true,
                    )
                },
                PageLevel::Level1 => unsafe {
                    PTPage::<Arch, Alloc>::split_leaf(
                        pte_ref,
                        level,
                        Page::<Size2MiB>::containing_address(start),
                        true,
                    )
                },
                PageLevel::Level2 => unsafe {
                    PTPage::<Arch, Alloc>::split_leaf(
                        pte_ref,
                        level,
                        Page::<Size1GiB>::containing_address(start),
                        true,
                    )
                },
                _ => return Err(PagingError::InvalidLevel),
            }?;
            let child = page.child(index).map_err(|_| PagingError::NotLeafEntry)?;
            drop(guard);
            self.unmap_region_child::<PL>(child, start, entry_end, state)?;
            start = entry_end;
        }
        Ok(())
    }

    /// Inputs: validated range and state; Requires: ordered bounds; Returns: unmap status.
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
        match MaxLevel::LEVEL {
            PageLevel::Level0 => self.unmap_region_l0(root, start, end, state),
            PageLevel::Level1 => self.unmap_region_level::<Lvl<1>>(root, start, end, state),
            PageLevel::Level2 => self.unmap_region_level::<Lvl<2>>(root, start, end, state),
            PageLevel::Level3 => self.unmap_region_level::<Lvl<3>>(root, start, end, state),
            PageLevel::Level4 => self.unmap_region_level::<Lvl<4>>(root, start, end, state),
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

    /// Removes the mapping of `page`, splitting a larger leaf first if needed.
    /// Arch mapping already represented by smaller leaves is not coalesced.
    /// `all_cpus` selects the synchronous flush scope for any split.
    #[inline(always)]
    pub fn unmap<PS: PageSize>(&self, page: Page<PS>, all_cpus: bool) -> UnmapEntryResult<Arch> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        if target == Self::SMALL {
            return self.unmap_4k_inner(Page::containing_address(vaddr), all_cpus);
        }
        self.unmap_with_split(page, all_cpus)
    }

    #[inline(always)]
    /// Inputs: 4 KiB page and flush scope; Requires: policy-approved address; Returns: old mapping.
    fn unmap_4k_inner(&self, page: Page<Size4KiB>, all_cpus: bool) -> UnmapEntryResult<Arch> {
        let vaddr = page.start_address();
        let mapping = self.root_view().walk(vaddr);
        if mapping.page.level() != Self::SMALL {
            return self.unmap_with_split(page, all_cpus);
        }

        let page_paddr = mapping.page_paddr();
        let _guard = self.wperms.lock(page_paddr);
        if !mapping.entry().load().is_leaf(Self::SMALL) {
            return Ok((None, MayNeedFlush::none()));
        }
        let entry = mapping.entry().swap(PTEntry::empty());
        Ok((Some(entry), PTPage::<Arch, Alloc>::flush_for_leaf(vaddr, Self::SMALL)))
    }

    /// Inputs: typed page and flush scope; Requires: policy-approved address; Returns: old mapping.
    fn unmap_with_split<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> UnmapEntryResult<Arch> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        let mut flush = MayNeedFlush::none();
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.page.level() < target {
                return Err(PagingError::NotLeafEntry);
            }
            let page_paddr = mapping.page_paddr();
            let _guard = self.wperms.lock(page_paddr);
            let entry = mapping.entry().load();
            if entry.is_table(mapping.page.level()) {
                continue;
            }
            if !entry.is_leaf(mapping.page.level()) {
                return Ok((None, flush));
            }
            if mapping.page.level() == target {
                let entry = mapping.entry().swap(PTEntry::empty());
                let pending = PTPage::<Arch, Alloc>::flush_for_leaf(vaddr, target);
                return Ok((Some(entry), flush.and(pending)));
            }
            drop(_guard);
            flush = flush.and(self.split(page, all_cpus)?);
        }
        unreachable!("unmap traversal exceeded the page-table depth")
    }

    /// Splits a huge leaf while preserving its mappings. New pages are prepared
    /// privately; the content guard covers publication and flushing.
    /// `page` may start anywhere within the selected mapping.
    /// `all_cpus = false` requires no affected translations on other CPUs and
    /// no migration during the operation.
    pub fn split<PS: PageSize>(
        &self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        match self.with_locked_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::split_leaf(entry, level, page, all_cpus)
        }) {
            Ok(flush) => Ok(flush),
            Err(PagingError::NotLeafEntry) => Ok(MayNeedFlush::none()),
            Err(err) => Err(err),
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
    /// Inputs: page, flags, and flush scope; Requires: present flags; Returns: flush obligation.
    fn set_flags_4k(
        &self,
        page: Page<Size4KiB>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let vaddr = page.start_address();
        let mapping = self.root_view().walk(vaddr);
        if mapping.page.level() != Self::SMALL {
            return self.with_locked_leaf(page, |entry, level| unsafe {
                PTPage::<Arch, Alloc>::update_leaf_flags_at(entry, level, page, flags, all_cpus)
            });
        }

        let page = mapping.page_paddr();
        let _guard = self.wperms.lock(page);
        let current = mapping.entry().load();
        if !current.is_leaf(Self::SMALL) {
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

    /// Inputs: validated bounds and flags; Requires: nonempty range; Returns: result and flush.
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
            descents_left: MaxLevel::DEPTH,
            descent_cursor: start,
            partial_leaves_left: 2,
        };
        loop {
            if let Some(result) = self.set_flags_range_step(end, flags, all_cpus, &mut state) {
                return result;
            }
        }
    }

    /// Inputs: range end, flags, and state; Requires: live cursor; Returns: completion if finished.
    fn set_flags_range_step(
        &self,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
        state: &mut RangeFlagsState<Arch::TlbFlushTok>,
    ) -> Option<RangeFlagsResult<Arch::TlbFlushTok>> {
        if state.cursor != state.descent_cursor {
            state.descent_cursor = state.cursor;
            state.descents_left = MaxLevel::DEPTH;
        }
        let mapping = self.root_view().walk(VirtAddr::from(state.cursor));
        if mapping.page.level() == Self::SMALL {
            return match self.set_flags_l0_run(
                &mapping.page,
                mapping.page_paddr(),
                mapping.index,
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
        let result = PTPage::<Arch, Alloc>::sweep_range(
            &self.root_view(),
            state.cursor,
            end,
            &mut |page, pte_ref, observed, level, entry_start, entry_end| {
                let current = if locked_page != Some(page) {
                    guard = None;
                    guard = Some(self.wperms.lock(page));
                    locked_page = Some(page);
                    pte_ref.load()
                } else {
                    observed
                };
                if current.is_table(level) {
                    return Err(RangeUpdateError::Descend);
                }
                if !current.is_leaf(level) {
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
                state.cursor = retry;
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
                        Page::<Size4KiB>::containing_address(split_address),
                        flags,
                        all_cpus,
                    ),
                    PageLevel::Level1 => self.update_flags(
                        Page::<Size2MiB>::containing_address(split_address),
                        flags,
                        all_cpus,
                    ),
                    PageLevel::Level2 => self.update_flags(
                        Page::<Size1GiB>::containing_address(split_address),
                        flags,
                        all_cpus,
                    ),
                    _ => Err(PagingError::InvalidLevel),
                };
                match update {
                    Ok(pending) => {
                        let flush = core::mem::replace(&mut state.flush, MayNeedFlush::none());
                        state.flush = flush.and(pending);
                        state.cursor = retry;
                        None
                    }
                    Err(error) => Some(state.finish(Err(error))),
                }
            }
            Err((_, RangeUpdateError::Paging(error))) => Some(state.finish(Err(error))),
        }
    }

    /// Inputs: L0 run and state; Requires: matching table; Returns: next cursor or error.
    fn set_flags_l0_run(
        &self,
        page: &PTPagePointer<'_, Arch, Alloc>,
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
            if !current.is_leaf(Self::SMALL) {
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

    /// Inputs: footprint and run bounds; Requires: nonempty changed run; Returns: nothing.
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

    /// Inputs: bounds and maximum level; Requires: nonempty range; Returns: largest covered level.
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

    /// Inputs: bounds, level, and alignment side; Requires: ordered bounds; Returns: fit decision.
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
    /// Inputs: page, flags, and flush scope; Requires: present flags; Returns: flush obligation.
    fn update_flags<PS: PageSize>(
        &self,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        if target == Self::SMALL {
            self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
            return self.set_flags_4k(Page::containing_address(vaddr), flags, all_cpus);
        }
        self.with_locked_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_at(entry, level, page, flags, all_cpus)
        })
    }

    /// Inputs: page and update callback; Requires: policy-approved address; Returns: callback result.
    fn with_locked_leaf<PS: PageSize>(
        &self,
        page: Page<PS>,
        update: impl FnOnce(
            PTEntryRef<'_, Arch>,
            PageLevel,
        ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError>,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let mapping = self.root_view().walk(vaddr);
            if mapping.page.level() < target {
                return Err(PagingError::NotLeafEntry);
            }
            let page = mapping.page_paddr();
            let _guard = self.wperms.lock(page);
            if mapping.entry().load().is_table(mapping.page.level()) {
                continue;
            }
            return update(mapping.entry(), mapping.page.level());
        }
        unreachable!("page-table update exceeded the tree depth")
    }

    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        let view = self.root_view();
        let entry = view.load(idx);
        entry.is_table(view.level()).then(|| PhysAddr::from(entry.address()))
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
        let unmapped_pages = range.len() * PS::SIZE / Size4KiB::SIZE;
        self.check_map_region(range, flags)
            .map_err(|error| MapRegionError { error, unmapped_pages })?;
        let mut state = RangeMapState::default();
        let root = self.root_view();
        self.do_map_region(&root, range, frames, flags, &mut state).map_err(|error| {
            MapRegionError { error, unmapped_pages: unmapped_pages - state.mapped_pages }
        })
    }

    /// Maps adjacent fixed-size 2 MiB and 4 KiB ranges in virtual-address order.
    /// A failure retains the mapped prefix across both ranges.
    pub fn map_region_mixed(
        &self,
        range_2m: PageRangeInclusive<Size2MiB>,
        frames_2m: &mut impl Iterator<Item = PhysFrame<Size2MiB>>,
        range_4k: PageRangeInclusive<Size4KiB>,
        frames_4k: &mut impl Iterator<Item = PhysFrame<Size4KiB>>,
        flags: Arch::PTFlags,
    ) -> Result<(), MapRegionError> {
        /// Inputs: two ranges; Requires: nonempty ranges; Returns: canonical adjacency decision.
        fn followed_by<A: PageSize, B: PageSize>(
            first: PageRangeInclusive<A>,
            second: PageRangeInclusive<B>,
        ) -> bool {
            first.end.start_address().bits() <= usize::MAX - A::SIZE
                && (first.end + 1).start_address() == second.start.start_address()
        }

        let pages_2m = range_2m.len() * Size2MiB::SIZE / Size4KiB::SIZE;
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
        unsafe {
            free_children(&self.root_view(), |index| self.tree.policy().owns_top_entry(index))
        };
    }
}
