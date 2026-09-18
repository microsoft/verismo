//! An owning page table with explicit mapping and TLB operations.
//! Live accesses are atomic through lifetime-bound views; private construction
//! uses ordinary memory. Mutations return TLB obligations to the caller.
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::mapping::{
    MappingMut, MappingMutOps, MappingRef, MappingRefOps, UnmapEntryResult,
};
use crate::structs::os_contract::{
    DirectMappedAllocator, MapRegionError, PagingAllocator, PagingError,
};
use crate::structs::page::{Page, PageRangeInclusive};
use crate::structs::policy::{KernelPolicy, PagingOwnershipPolicy, UserPolicy};
use crate::structs::ptpage::{
    free_children, reclaim_path, reclaim_range, FlushFootprint, PTPage, PTPagePointer, PTPageTree,
    Translation,
};
use crate::structs::sizes::{
    entry_index, next_boundary, page_level_for_size, PageSize, Size1GiB, Size2MiB, Size4KiB,
    PT_ENTRY_COUNT,
};
use crate::structs::tlb::MayNeedFlush;

#[derive(Default)]
struct RangeMapState {
    mapped_pages: usize,
}

struct RangeUnmapState<'a> {
    all_mapped: &'a mut bool,
    footprint: &'a mut FlushFootprint,
}

/// Arch page table rooted at `MaxLevel`: `Lvl<3>` is four-level x86-64
/// paging, `Lvl<4>` five-level. Drop frees the root and owned descendant
/// tables, never shared subtrees or mapped data frames. Use `ManuallyDrop`
/// or [`PageTable::leak`] while external owners or hardware still use them.
pub struct PageTable<
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: LevelSpec,
    Owned: PagingOwnershipPolicy = KernelPolicy,
> {
    tree: PTPageTree<Arch, Alloc, MaxLevel, Owned>,
}

/// Arch kernel page table that owns every attached subtree.
pub type KernelPageTable<Arch, Alloc, MaxLevel> = PageTable<Arch, Alloc, MaxLevel, KernelPolicy>;
/// Arch user page table that borrows the configured kernel root entries.
pub type UserPageTable<'kernel, Arch, Alloc, MaxLevel, const START: usize, const END: usize> =
    PageTable<Arch, Alloc, MaxLevel, UserPolicy<'kernel, START, END>>;

impl<Arch: ArchPagingMeta, Alloc: DirectMappedAllocator, MaxLevel: LevelSpec>
    PageTable<Arch, Alloc, MaxLevel>
{
    /// Arch table that direct-maps the region the allocator allocates from, at the
    /// addresses the allocator gives for it.
    ///
    /// Mapping the whole region up front is what the tree needs to describe
    /// itself: its own pages come out of that region, as does every table it
    /// allocates later. Initialization and self-mapping checks use ordinary
    /// accesses while the entire tree is still private.
    pub fn new(flags: Arch::PTFlags) -> Result<Self, PagingError> {
        let root_pa = PTPage::<Arch, Alloc>::new_direct_mapped(MaxLevel::LEVEL, flags)?;
        // SAFETY: construction produced a validated, exclusively owned, unpublished tree.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree })
    }
}

impl<Arch: ArchPagingMeta, Alloc: PagingAllocator, MaxLevel: LevelSpec>
    PageTable<Arch, Alloc, MaxLevel>
{
    /// Validates an existing root before constructing its controller.
    /// Rejection or validation unwinding leaves the root allocated.
    /// # Safety
    /// Keep the initialized, correctly leveled, acyclic tree at clean `root_pa`
    /// accessible and aligned for `PTPage` for this controller's lifetime.
    /// Exclude other software access during mutations and entire mutable-handle
    /// lifetimes, including across roots.
    /// Shared pages must have identical virtual prefixes, never other aliases.
    /// Only allow Drop when the root and every descendant table are exclusively
    /// owned, allocator-allocated, and have no software or hardware users;
    /// otherwise use `ManuallyDrop` or [`Self::leak`].
    pub unsafe fn from_root(root_pa: PhysAddr) -> Result<Self, PagingError> {
        unsafe {
            PTPage::<Arch, Alloc>::validate_tree(root_pa, MaxLevel::LEVEL, |pte_ref| {
                PTEntryRef::from_raw(pte_ref.cast_mut()).load()
            })
        }?;
        // SAFETY: validation establishes shape; ownership and quiescence are the caller's duty.
        let tree = unsafe { PTPageTree::from_root(root_pa, KernelPolicy) };
        Ok(Self { tree })
    }
}

impl<
        Arch: ArchPagingMeta,
        Alloc: PagingAllocator,
        MaxLevel: LevelSpec,
        Owned: PagingOwnershipPolicy,
    > PageTable<Arch, Alloc, MaxLevel, Owned>
{
    /// Confirms the tree maps each of its own table pages, the root included,
    /// at the address the allocator hands out for it, so that a walk still
    /// reaches them once the tree is installed.
    pub fn validate_page_table(&self) -> Result<(), PagingError> {
        // SAFETY: this borrow keeps the tree accessible throughout validation.
        unsafe {
            PTPage::<Arch, Alloc>::validate_tree(
                self.tree.root_paddr(),
                MaxLevel::LEVEL,
                |pte_ref| PTEntryRef::from_raw(pte_ref.cast_mut()).load(),
            )
        }
    }
}

impl<Arch: ArchPagingMeta, Alloc: PagingAllocator, MaxLevel: LevelSpec>
    PageTable<Arch, Alloc, MaxLevel>
{
    /// Borrows existing subtrees at `START..END`; the entire range becomes immutable.
    /// Initialize shared root entries before copying if later growth must be visible.
    /// # Safety
    /// `Alloc` must resolve shared physical addresses to the same table pages as `other`.
    /// Shared pages must remain allocated while either tree links to them.
    /// Exclude access through every alias during mutations and the entire
    /// lifetime of any mutable mapping handle. Cleanup through either tree
    /// requires removing all other parent links to every reclaimed page.
    pub unsafe fn new_from_sharing_top<'kernel, const START: usize, const END: usize>(
        other: &'kernel Self,
    ) -> Result<UserPageTable<'kernel, Arch, Alloc, MaxLevel, START, END>, PagingError> {
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
        let this = PageTable { tree };
        this.validate_page_table()?;
        Ok(this)
    }

    /// Gives up ownership of the tree and returns its root. What
    /// a table installed in a control register needs: dropping it would free a
    /// page the hardware still walks. Arch borrowed root remains borrowed.
    pub fn leak(self) -> PhysAddr {
        let (_, root_pa) = self.leak_parts();
        root_pa
    }

    /// Raw staged edits are restricted to privileged controllers.
    /// # Safety
    /// Committed entries must preserve the tree's level, validity and ownership
    /// invariants. New table links transfer exclusive ownership of initialized,
    /// correctly leveled, allocator-allocated subtrees; no aliases or cycles.
    /// Present entries must retain their output frame and address tags.
    /// Coordinate hardware access and flushes for every published change.
    ///
    /// ```compile_fail,E0133
    /// use paging::address::VirtAddr;
    /// use paging::level::LevelSpec;
    /// use paging::os_contract::PagingAllocator;
    /// use paging::pagetable::PageTable;
    /// use paging::ArchPagingMeta;
    ///
    /// fn raw_edit<Arch: ArchPagingMeta, Alloc: PagingAllocator, MaxLevel: LevelSpec>(
    ///     table: &mut PageTable<Arch, Alloc, MaxLevel>,
    ///     address: VirtAddr,
    /// ) {
    ///     let _ = table.walk_mut(address);
    /// }
    /// ```
    pub unsafe fn walk_mut(&mut self, vaddr: VirtAddr) -> MappingMut<'_, Arch> {
        self.walk_mut_inner(vaddr)
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
        assert!(idx < PT_ENTRY_COUNT);
        if MaxLevel::LEVEL.is_leaf() {
            return Err(PagingError::InvalidLevel);
        }
        let desired = PTEntry::<Arch>::new_table(
            Arch::make_private_address(subpage_pa),
            Arch::PTFlags::parent_flags(),
        );
        let view = self.root_view();
        let pte_ref = view.entry(idx);
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

        pte_ref.store(desired);
        Ok(true)
    }
}

impl<
        'kernel,
        Arch: ArchPagingMeta,
        Alloc: PagingAllocator,
        MaxLevel: LevelSpec,
        const START: usize,
        const END: usize,
    > PageTable<Arch, Alloc, MaxLevel, UserPolicy<'kernel, START, END>>
{
    /// The returned policy retains the kernel borrow while the raw tree is used.
    pub fn leak(self) -> (UserPolicy<'kernel, START, END>, PhysAddr) {
        self.leak_parts()
    }
}

impl<
        Arch: ArchPagingMeta,
        Alloc: PagingAllocator,
        MaxLevel: LevelSpec,
        Owned: PagingOwnershipPolicy,
    > PageTable<Arch, Alloc, MaxLevel, Owned>
{
    fn leak_parts(self) -> (Owned, PhysAddr) {
        self.tree.into_parts()
    }

    pub fn root_paddr(&self) -> PhysAddr {
        self.tree.root_paddr()
    }

    fn root_view(&self) -> PTPagePointer<'_, Arch, Alloc> {
        self.tree.root()
    }

    /// Where `vaddr` comes to rest: a handle on the first entry the hardware
    /// would not walk through, which is a mapping, an absent entry, or an entry
    /// at the leaf level, where bit 7 is PAT rather than PS.
    ///
    /// ```compile_fail,E0502
    /// use paging::address::VirtAddr;
    /// use paging::level::LevelSpec;
    /// use paging::mapping::MappingRefOps;
    /// use paging::os_contract::PagingAllocator;
    /// use paging::pagetable::KernelPageTable;
    /// use paging::ArchPagingMeta;
    ///
    /// fn reclaim<Arch: ArchPagingMeta, Alloc: PagingAllocator, MaxLevel: LevelSpec>(
    ///     table: &mut KernelPageTable<Arch, Alloc, MaxLevel>,
    ///     address: VirtAddr,
    /// ) {
    ///     let entry = table.walk(address);
    ///     unsafe { table.free_page_table_by_addr(address) };
    ///     let _ = entry.read();
    /// }
    /// ```
    pub fn walk(&self, vaddr: VirtAddr) -> MappingRef<'_, Arch> {
        let (entry, level) = self.walk_entry(vaddr);
        MappingRef::from_view(level, entry)
    }

    fn walk_entry(&self, vaddr: VirtAddr) -> (PTEntryRef<'_, Arch>, PageLevel) {
        let observed = self.tree.root().walk(vaddr);
        (observed.entry(), observed.page.level())
    }

    fn leaf_entry(paddr: PhysAddr, target: PageLevel, flags: Arch::PTFlags) -> PTEntry<Arch> {
        let addr = Arch::make_private_address(paddr);
        let flags = Arch::filter_flags(flags);
        let flags = if target.is_leaf() { flags } else { flags.with(Arch::PTFlags::HUGE) };
        PTEntry::new(addr, flags)
    }

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

    fn map_leaf_run<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>>(
        &mut self,
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
        for index in start_index..=end_index {
            let observed = page.load(index);
            if observed.is_table(target) {
                return Err(PagingError::NotLeafEntry);
            }
            if observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level: target });
            }
        }
        let mapped_pages = PS::SIZE / Size4KiB::SIZE;
        for index in start_index..=end_index {
            let frame = frames.next().ok_or(PagingError::InvalidRange)?;
            page.store(index, Self::leaf_entry(frame.start_address(), target, flags));
            state.mapped_pages += mapped_pages;
        }
        Ok(())
    }

    fn mapping_child<'tree>(
        &mut self,
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
        parent.store(
            index,
            PTEntry::new_table(Arch::make_private_address(prepared.root_paddr()), parent_flags),
        );
        prepared.release();
        parent.child(index).map_err(|_| PagingError::NotLeafEntry)
    }

    #[inline(always)]
    fn do_map_region<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>>(
        &mut self,
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
    fn unmap_region_l0(
        &mut self,
        page: PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        debug_assert_eq!(page.level(), PageLevel::Level0);
        let mut index = entry_index(start, PageLevel::Level0);
        let mut first_changed = None;
        let mut last_changed = start;
        while start < end {
            let pte_ref = page.entry(index);
            if pte_ref.load().is_leaf(PageLevel::Level0) {
                pte_ref.swap(PTEntry::empty());
                if first_changed.is_none() {
                    first_changed = Some(start);
                }
                last_changed = start;
            } else {
                *state.all_mapped = false;
            }
            start = next_boundary(start, PageLevel::Level0, end);
            index = (index + 1) & (PT_ENTRY_COUNT - 1);
        }
        if let Some(first) = first_changed {
            state.footprint.include(first, PageLevel::Level0);
            state.footprint.include(last_changed, PageLevel::Level0);
        }
        Ok(())
    }

    #[inline(always)]
    fn unmap_region_child<PL: InnerLevel>(
        &mut self,
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
    fn unmap_region_level<PL: InnerLevel>(
        &mut self,
        page: PTPagePointer<'_, Arch, Alloc>,
        mut start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        let level = PL::LEVEL;
        debug_assert_eq!(page.level(), level);
        while start < end {
            let entry_end = next_boundary(start, level, end);
            let index = entry_index(start, level);
            let pte_ref = page.entry(index);
            let observed = pte_ref.load();
            if observed.is_table(level) {
                let child =
                    page.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry)?;
                self.unmap_region_child::<PL>(child, start, entry_end, state)?;
                start = entry_end;
                continue;
            }
            if !observed.is_leaf(level) {
                *state.all_mapped = false;
                start = entry_end;
                continue;
            }
            if start.is_aligned(level.size()) && end - start >= level.size() {
                pte_ref.swap(PTEntry::empty());
                state.footprint.include(start, level);
                start = entry_end;
                continue;
            }

            // SAFETY: the exclusive controller borrow pins the pte_ref and excludes writers.
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
            self.unmap_region_child::<PL>(child, start, entry_end, state)?;
            start = entry_end;
        }
        Ok(())
    }

    fn unmap_region_sweep(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        if start == end {
            return Ok(());
        }
        let root_paddr = self.tree.root_paddr();
        // SAFETY: the exclusive controller borrow pins the root and all descendants.
        let root = unsafe { PTPagePointer::from_root(root_paddr, MaxLevel::LEVEL) };
        match MaxLevel::LEVEL {
            PageLevel::Level0 => self.unmap_region_l0(root, start, end, state),
            PageLevel::Level1 => self.unmap_region_level::<Lvl<1>>(root, start, end, state),
            PageLevel::Level2 => self.unmap_region_level::<Lvl<2>>(root, start, end, state),
            PageLevel::Level3 => self.unmap_region_level::<Lvl<3>>(root, start, end, state),
            PageLevel::Level4 => self.unmap_region_level::<Lvl<4>>(root, start, end, state),
        }
    }

    fn walk_mut_inner(&mut self, vaddr: VirtAddr) -> MappingMut<'_, Arch> {
        let (entry, level) = self.walk_entry(vaddr);
        MappingMut::from_view(Some(vaddr), level, entry)
    }

    /// The frame `vaddr` translates to, at whatever page size maps it.
    #[inline(always)]
    pub fn translate(&self, vaddr: VirtAddr) -> Result<Translation<Arch>, PagingError> {
        let mapping = self.walk(vaddr);
        let entry = mapping.read();
        let level = mapping.level();
        if !entry.is_leaf(level) {
            return Err(PagingError::NotMapped);
        }
        let offset = vaddr.bits() & (level.size() - 1);
        Ok(Translation::new(
            PhysAddr::from((entry.paddr_field() & !(level.size() - 1)) + offset),
            level,
        ))
    }

    /// The clean physical address `vaddr` translates to.
    #[inline(always)]
    pub fn phys_addr(&self, vaddr: VirtAddr) -> Result<PhysAddr, PagingError> {
        self.translate(vaddr).map(|frame| frame.address())
    }

    /// Maps `page` to the matching physical `frame`, building intermediate
    /// tables with `parent_flags`. Existing mappings are never overwritten.
    pub fn map_with_parent_flags<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: Arch::PTFlags,
        shared: bool,
        parent_flags: Arch::PTFlags,
    ) -> Result<(), PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target.depth() > MaxLevel::DEPTH {
            return Err(PagingError::InvalidLevel);
        }
        let (entry, level) = self.walk_entry(vaddr);
        if level > target && !entry.load().present() {
            let child_level = level.child().ok_or(PagingError::InvalidLevel)?;
            let prepared = PTPageTree::<Arch, Alloc>::new(child_level)?;
            let observed = prepared.root().walk(vaddr);
            MappingMut::from_view(Some(vaddr), observed.page.level(), observed.entry())
                .commit_no_flush(|map| {
                    PTPage::<Arch, Alloc>::do_map(map, page, frame, flags, shared, parent_flags)
                })?;
            entry.store(PTEntry::new_table(
                Arch::make_private_address(prepared.root_paddr()),
                Arch::filter_flags(parent_flags),
            ));
            prepared.release();
            return Ok(());
        }
        MappingMut::from_view(Some(vaddr), level, entry).commit_no_flush(|map| {
            PTPage::<Arch, Alloc>::do_map(map, page, frame, flags, shared, parent_flags)
        })
    }

    /// [`Self::map_with_parent_flags`] with the architecture's default flags
    /// for intermediate tables.
    pub fn map<PS: PageSize>(
        &mut self,
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
    pub fn unmap<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> UnmapEntryResult<Arch> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        self.tree.policy().check_address(MaxLevel::LEVEL, vaddr)?;
        if target > MaxLevel::LEVEL {
            return Err(PagingError::InvalidLevel);
        }
        let mut flush = MayNeedFlush::none();
        for _ in 0..=MaxLevel::LEVEL.depth() {
            let (entry, level) = self.walk_entry(vaddr);
            let current = entry.load();
            if level < target {
                return Err(PagingError::NotLeafEntry);
            }
            if !current.is_leaf(level) {
                return Ok((None, flush));
            }
            if level == target {
                let removed = entry.swap(PTEntry::empty());
                let pending = PTPage::<Arch, Alloc>::flush_for_leaf(vaddr, target);
                return Ok((Some(removed), flush.and(pending)));
            }
            // SAFETY: the exclusive borrow pins the entry and excludes software writers.
            let pending =
                unsafe { PTPage::<Arch, Alloc>::split_leaf(entry, level, page, all_cpus) }?;
            flush = flush.and(pending);
        }
        unreachable!("unmap traversal exceeded the page-table depth")
    }

    /// Splits a huge leaf without changing its mappings. The complete split
    /// path is prepared privately, so allocation failure leaves the leaf intact.
    /// `page` may start anywhere within the selected mapping.
    /// Splitting uses the architecture's required publication and flush order.
    /// `all_cpus = false` requires no affected translations on other CPUs and
    /// no migration during the operation.
    pub fn split<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        match self.with_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::split_leaf(entry, level, page, all_cpus)
        }) {
            Ok(flush) => Ok(flush),
            Err(PagingError::NotLeafEntry) => Ok(MayNeedFlush::none()),
            Err(err) => Err(err),
        }
    }

    /// Replaces flags on exactly one typed page, splitting a larger
    /// leaf if needed. Frame, tags, PAT and Arch/D history are retained.
    /// `all_cpus` selects the synchronous flush scope as in [`Self::split`].
    pub fn set_flags<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        if !flags.present() {
            return Err(PagingError::InvalidFlags);
        }
        self.with_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_at(entry, level, page, flags, all_cpus)
        })
    }

    /// Replaces flags across a page-aligned range. On error, earlier edits remain applied
    /// and their flush obligation is returned alongside the error.
    /// Page-size transitions share one architecture-ordered synchronous flush.
    /// `all_cpus` selects its scope as in [`Self::split`].
    pub fn set_flags_range(
        &mut self,
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
        // SAFETY: the exclusive borrow pins the tree and excludes software writers.
        unsafe {
            PTPage::<Arch, Alloc>::update_leaf_flags_range(
                self.root_view(),
                start,
                end,
                flags,
                all_cpus,
            )
        }
    }

    fn with_leaf<PS: PageSize>(
        &mut self,
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
        let (entry, level) = self.walk_entry(vaddr);
        update(entry, level)
    }
}

impl<
        Arch: ArchPagingMeta,
        Alloc: PagingAllocator,
        MaxLevel: LevelSpec,
        Owned: PagingOwnershipPolicy,
    > PageTable<Arch, Alloc, MaxLevel, Owned>
{
    const SMALL: PageLevel = PageLevel::Level0;

    /// Retags `page` as shared, splitting any larger mapping it lies in.
    /// Discharge the returned flush unless BBM completes it synchronously.
    /// `all_cpus` selects the scope only when the architecture requires BBM.
    pub fn set_shared<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.with_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_encryption_leaf(entry, level, page, true, all_cpus)
        })
    }

    /// Retags `page` as private, splitting as [`Self::set_shared`] does.
    /// Discharge the returned flush unless BBM completes it synchronously.
    /// `all_cpus` selects the scope only when the architecture requires BBM.
    pub fn set_private<PS: PageSize>(
        &mut self,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<Arch::TlbFlushTok>, PagingError> {
        self.with_leaf(page, |entry, level| unsafe {
            PTPage::<Arch, Alloc>::update_encryption_leaf(entry, level, page, false, all_cpus)
        })
    }

    /// The table entry `idx` of the root points at, or `None` if it points at
    /// no table.
    pub fn next_table_pa(&self, idx: usize) -> Option<PhysAddr> {
        assert!(idx < PT_ENTRY_COUNT);
        let view = self.root_view();
        let entry = view.load(idx);
        if !entry.is_table(view.level()) {
            return None;
        }
        Some(PhysAddr::from(entry.address()))
    }

    /// Maps each page in `range` to the next frame. A failure retains the
    /// mapped prefix and reports the remaining number of 4 KiB pages.
    pub fn map_region<PS: PageSize>(
        &mut self,
        range: PageRangeInclusive<PS>,
        frames: &mut impl Iterator<Item = PhysFrame<PS>>,
        flags: Arch::PTFlags,
    ) -> Result<(), MapRegionError> {
        let unmapped_pages = range.len() * PS::SIZE / Size4KiB::SIZE;
        self.check_map_region(range, flags)
            .map_err(|error| MapRegionError { error, unmapped_pages })?;
        let root_paddr = self.tree.root_paddr();
        // SAFETY: the exclusive controller borrow pins the root and all descendants.
        let root = unsafe { PTPagePointer::from_root(root_paddr, MaxLevel::LEVEL) };
        let mut state = RangeMapState::default();
        self.do_map_region(&root, range, frames, flags, &mut state).map_err(|error| {
            MapRegionError { error, unmapped_pages: unmapped_pages - state.mapped_pages }
        })
    }

    /// Maps adjacent fixed-size 2 MiB and 4 KiB ranges in virtual-address order.
    /// A failure retains the mapped prefix across both ranges.
    pub fn map_region_mixed(
        &mut self,
        range_2m: PageRangeInclusive<Size2MiB>,
        frames_2m: &mut impl Iterator<Item = PhysFrame<Size2MiB>>,
        range_4k: PageRangeInclusive<Size4KiB>,
        frames_4k: &mut impl Iterator<Item = PhysFrame<Size4KiB>>,
        flags: Arch::PTFlags,
    ) -> Result<(), MapRegionError> {
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
        &mut self,
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

    /// Frees owned tables left empty in `[start, end)`, skipping shared subtrees.
    ///
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_range(&mut self, start: VirtAddr, end: VirtAddr) {
        assert!(start <= end);
        if start < end {
            let span = MaxLevel::LEVEL.size() * PT_ENTRY_COUNT;
            let first = start.bits() & (span - 1);
            let last = ((end.bits() - 1) & (span - 1)) + 1;
            assert!(first < last, "range wraps the root's address space");
            // SAFETY: the caller supplies ownership and excludes all walkers.
            unsafe {
                reclaim_range(
                    &self.root_view(),
                    first,
                    last,
                    |index| self.tree.policy().owns_top_entry(index),
                    // Exclusive access makes every non-present word unreachable.
                    |entry| !entry.present(),
                )
            };
        }
    }

    /// Frees the tables left empty by unmapping `vaddr`, walking the one path
    /// down to it rather than a range, and reports how many it freed.
    /// Tables still holding mappings remain allocated.
    ///
    /// # Safety
    /// Every reclaimed page must come from this allocator and have no parent
    /// links except those removed here. Exclude all other walkers, discharge
    /// leaf flushes, and invalidate cached table pointers before reuse/resume.
    pub unsafe fn free_page_table_by_addr(&mut self, vaddr: VirtAddr) -> usize {
        if !self.tree.policy().owns_top_entry(entry_index(vaddr, MaxLevel::LEVEL)) {
            return 0;
        }
        // SAFETY: the caller's obligation is this function's.
        // Exclusive access makes every non-present word unreachable.
        unsafe { reclaim_path(&self.root_view(), vaddr, |entry| !entry.present()) }
    }

    /// Frees owned tables below the root; borrowed root entries remain intact.
    ///
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
