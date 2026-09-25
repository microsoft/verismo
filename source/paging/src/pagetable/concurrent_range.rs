//! Concurrent range operations: `map_region`, `unmap_region`,
//! `set_flags_range`, and `cleanup_page_tables_by_range`.

use super::concurrent::{LockSpec, PageTable};
use crate::structs::address::{Address, PhysAddr, VirtAddr, LOW_CANONICAL_END};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::PTEntry;
use crate::structs::frame::PhysFrame;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{MapRegionError, PagingAllocator, PagingError};
use crate::structs::page::{Page, PageRangeInclusive};
use crate::structs::policy::{KernelPolicy, OwnedIndices, PagingOwnershipPolicy};
use crate::structs::ptpage::{
    DetachedPageTable, FlushFootprint, PTPageRef, PTPageTree, WalkLevel, WalkLevelImpl,
};
use crate::structs::sizes::{entry_index, Huge, PageSize, Regular, SizeLevel2, PT_ENTRY_COUNT};
use crate::structs::tlb::{with_detach_batch, DetachBatch, MayNeedFlush, TlbFlush};

const DETACHED_TABLE_BATCH_CAPACITY: usize = 64;

struct RangeUnmapState<'a> {
    all_mapped: &'a mut bool,
    footprint: &'a mut FlushFootprint,
}

struct RangeFlagsState<T: TlbFlush> {
    flush: MayNeedFlush<T>,
    footprint: FlushFootprint,
}

impl<T: TlbFlush> RangeFlagsState<T> {
    fn finish(&mut self, result: Result<(), PagingError>) -> RangeFlagsResult<T> {
        let flush = core::mem::replace(&mut self.flush, MayNeedFlush::none());
        (result, flush.and(self.footprint.token()))
    }
}

type RangeFlagsResult<T> = (Result<(), PagingError>, MayNeedFlush<T>);

impl<Arch, Alloc, MaxLevel, WP, T, Owned> PageTable<Arch, Alloc, MaxLevel, WP, T, Owned>
where
    Arch: ArchPagingMeta,
    Alloc: PagingAllocator,
    MaxLevel: WalkLevel,
    WP: LockSpec<T>,
    Owned: PagingOwnershipPolicy,
{
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
        page: &PTPageRef<'_, Arch, Alloc, L>,
        pages: PageRangeInclusive<PS>,
        frames: &mut I,
        flags: Arch::PTFlags,
        mapped_ps_pages: &mut usize,
    ) -> Result<(), PagingError> {
        let target = page.level();
        debug_assert_eq!(target.size(), PS::SIZE);
        let start_index = pages.start.pt_index();
        let end_index = pages.end.pt_index();
        debug_assert!(start_index <= end_index);

        {
            let write = page.lock_to_update(&self.wperms);
            for index in start_index..=end_index {
                let observed = write.load(index);
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

        let mut write = page.lock_to_update(&self.wperms);
        for index in start_index..start_index + count {
            let observed = write.load(index);
            if observed.is_present_table(target) {
                return Err(PagingError::NotLeafEntry);
            }
            if observed.present() {
                return Err(PagingError::EntryAlreadyPresent { level: target });
            }
        }
        for (offset, frame) in buffered[..count].iter().enumerate() {
            let frame = frame.expect("buffered frame");
            let index = start_index + offset;
            write.install_leaf(index, Self::leaf_entry(frame.start_address(), target, flags))?;
            *mapped_ps_pages += 1;
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
        parent: &PTPageRef<'tree, Arch, Alloc, L>,
        index: usize,
    ) -> Result<PTPageRef<'tree, Arch, Alloc, L::ChildLevel>, PagingError> {
        let observed = parent.load(index);
        if observed.is_present_table(parent.level()) {
            return parent.child_from_observed(observed).map_err(|_| PagingError::NotLeafEntry);
        }
        if observed.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
        }

        let parent_flags = Arch::filter_flags(Arch::PTFlags::parent_flags());
        let prepared = PTPageTree::<Arch, Alloc, L::ChildLevel>::new_root(KernelPolicy::new())?;
        let mut write = parent.lock_to_update(&self.wperms);
        let current = write.load(index);
        if current.is_present_table(parent.level()) {
            return parent.child_from_observed(current).map_err(|_| PagingError::NotLeafEntry);
        }
        if current.present() {
            return Err(PagingError::EntryAlreadyPresent { level: parent.level() });
        }
        let installed =
            PTEntry::new_table(Arch::make_private_address(prepared.root_paddr()), parent_flags);
        write.publish_table(index, installed)?;
        prepared.release();
        parent.child_from_observed(installed).map_err(|_| PagingError::NotLeafEntry)
    }

    /// Partitions the range by table entry and descends through statically typed child levels.
    #[inline(always)]
    fn map_range_from<PS: PageSize, I: Iterator<Item = PhysFrame<PS>>, L: WalkLevelImpl>(
        &self,
        ptpage: &PTPageRef<'_, Arch, Alloc, L>,
        range: PageRangeInclusive<PS>,
        frames: &mut I,
        flags: Arch::PTFlags,
        mapped_ps_pages: &mut usize,
    ) -> Result<(), PagingError> {
        let level = L::LEVEL;
        if level.size() == PS::SIZE {
            return self.map_leaf_run(ptpage, range, frames, flags, mapped_ps_pages);
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
            self.map_range_from(
                &child,
                Page::range_inclusive(start, end),
                frames,
                flags,
                mapped_ps_pages,
            )?;
            if end.start_address() == range.end.start_address() {
                return Ok(());
            }
            start = end + 1;
        }
        unreachable!("range spans more entries than one page-table page")
    }

    /// Unmaps one range segment through typed child recursion.
    #[inline(always)]
    fn unmap_range_from<L: WalkLevelImpl>(
        &self,
        page: &PTPageRef<'_, Arch, Alloc, L>,
        start: usize,
        end: usize,
        state: &mut RangeUnmapState<'_>,
    ) -> Result<(), PagingError> {
        if start >= end {
            return Ok(());
        }

        let level = L::LEVEL;
        if level == PageLevel::Level0 {
            let first = entry_index(VirtAddr::from(start), level);
            let last = entry_index(VirtAddr::from(end - 1), level);
            let mut first_changed = None;
            let mut last_changed = start;
            let mut cursor = start;
            let mut write = page.lock_to_update(&self.wperms);
            for index in first..=last {
                if matches!(write.take_leaf(index), Ok(Some(_))) {
                    first_changed.get_or_insert(cursor);
                    last_changed = cursor;
                } else {
                    *state.all_mapped = false;
                }
                cursor = cursor.saturating_add(level.size());
            }
            if let Some(first) = first_changed {
                state.footprint.include(VirtAddr::from(first), level);
                state.footprint.include(VirtAddr::from(last_changed), level);
            }
            return Ok(());
        }

        let mut cursor = start;
        while cursor < end {
            let index = entry_index(VirtAddr::from(cursor), level);
            let base = cursor & !(level.size() - 1);
            let next = base.saturating_add(level.size()).min(end);
            let observed = page.load(index);
            if let Ok(child) = page.child_from_observed(observed) {
                self.unmap_range_from(&child, cursor, next, state)?;
                cursor = next;
                continue;
            }
            let child = {
                let mut write = page.lock_to_update(&self.wperms);
                let current = write.load(index);
                if current.is_present_table(level) {
                    Some(current)
                } else if !current.is_present_leaf(level) {
                    *state.all_mapped = false;
                    None
                } else if cursor == base && next == base.saturating_add(level.size()) {
                    let removed = write.take_leaf(index).expect("locked leaf remains a leaf");
                    debug_assert!(removed.is_some());
                    state.footprint.include(VirtAddr::from(cursor), level);
                    None
                } else {
                    // SAFETY: the content guard pins the entry and excludes competing writers.
                    unsafe { write.split_leaf_for_region(index, VirtAddr::from(cursor))? };
                    Some(write.load(index))
                }
            };
            if let Some(entry) = child {
                let child =
                    page.child_from_observed(entry).map_err(|_| PagingError::NotLeafEntry)?;
                self.unmap_range_from(&child, cursor, next, state)?;
            }
            cursor = next;
        }
        Ok(())
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

    /// Updates one validated range through typed child recursion.
    fn set_flags_range_inner(
        &self,
        start: usize,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
    ) -> RangeFlagsResult<Arch::TlbFlushTok> {
        let mut state =
            RangeFlagsState { flush: MayNeedFlush::none(), footprint: FlushFootprint::default() };
        let root = self.root_view();
        let high_start = VirtAddr::new(LOW_CANONICAL_END).bits();
        let result = if start < LOW_CANONICAL_END && end >= high_start {
            self.set_flags_range_from(&root, start, LOW_CANONICAL_END, flags, all_cpus, &mut state)
                .and_then(|()| {
                    self.set_flags_range_from(&root, high_start, end, flags, all_cpus, &mut state)
                })
        } else {
            self.set_flags_range_from(&root, start, end, flags, all_cpus, &mut state)
        };
        state.finish(result)
    }

    /// Updates one canonical range segment without restarting from the root.
    #[inline(always)]
    fn set_flags_range_from<L: WalkLevelImpl>(
        &self,
        page: &PTPageRef<'_, Arch, Alloc, L>,
        start: usize,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
        state: &mut RangeFlagsState<Arch::TlbFlushTok>,
    ) -> Result<(), PagingError> {
        if start >= end {
            return Ok(());
        }

        let level = L::LEVEL;
        if level == PageLevel::Level0 {
            return self.set_flags_l0_run(page, start, end, flags, state);
        }

        let mut cursor = start;
        while cursor < end {
            let index = entry_index(VirtAddr::from(cursor), level);
            let base = cursor & !(level.size() - 1);
            let next = base.saturating_add(level.size()).min(end);
            let observed = page.load(index);
            if let Ok(child) = page.child_from_observed(observed) {
                self.set_flags_range_from(&child, cursor, next, flags, all_cpus, state)?;
                cursor = next;
                continue;
            }
            if let Some(entry) =
                self.set_flags_non_table(page, cursor, next, flags, all_cpus, state)?
            {
                let child =
                    page.child_from_observed(entry).map_err(|_| PagingError::NotLeafEntry)?;
                self.set_flags_range_from(&child, cursor, next, flags, all_cpus, state)?;
            }
            cursor = next;
        }
        Ok(())
    }

    /// Updates a locked leaf or returns a table observed during recheck.
    #[inline(never)]
    fn set_flags_non_table<L: WalkLevelImpl>(
        &self,
        page: &PTPageRef<'_, Arch, Alloc, L>,
        start: usize,
        end: usize,
        flags: Arch::PTFlags,
        all_cpus: bool,
        state: &mut RangeFlagsState<Arch::TlbFlushTok>,
    ) -> Result<Option<PTEntry<Arch>>, PagingError> {
        let level = L::LEVEL;
        let index = entry_index(VirtAddr::from(start), level);
        let mut write = page.lock_to_update(&self.wperms);
        let current = write.load(index);
        if current.is_present_table(level) {
            return Ok(Some(current));
        }
        if !current.is_present_leaf(level) {
            return Err(PagingError::NotMapped);
        }
        let base = start & !(level.size() - 1);
        if start == base && end == base.saturating_add(level.size()) {
            if write.set_leaf_flags(index, flags)? {
                state.footprint.include(VirtAddr::from(start), level);
            }
            return Ok(None);
        }

        let align_end = start == base;
        let target = Self::largest_covered_level(start, end, level, align_end);
        let address = if align_end { end - target.size() } else { start };
        let address = VirtAddr::from(address);
        // SAFETY: the content guard pins the entry and excludes competing writers.
        let pending = unsafe {
            match target {
                PageLevel::Level0 => write.update_leaf_flags_at(
                    index,
                    Page::<Regular>::containing_address(address),
                    flags,
                    all_cpus,
                ),
                PageLevel::Level1 => write.update_leaf_flags_at(
                    index,
                    Page::<Huge>::containing_address(address),
                    flags,
                    all_cpus,
                ),
                PageLevel::Level2 => write.update_leaf_flags_at(
                    index,
                    Page::<SizeLevel2>::containing_address(address),
                    flags,
                    all_cpus,
                ),
                _ => Err(PagingError::InvalidLevel),
            }
        }?;
        let accumulated = core::mem::replace(&mut state.flush, MayNeedFlush::none());
        state.flush = accumulated.and(pending);
        Ok(Some(write.load(index)))
    }

    /// Updates one L0 run under one page lock.
    #[inline(always)]
    fn set_flags_l0_run<L: WalkLevelImpl>(
        &self,
        page: &PTPageRef<'_, Arch, Alloc, L>,
        start: usize,
        end: usize,
        flags: Arch::PTFlags,
        state: &mut RangeFlagsState<Arch::TlbFlushTok>,
    ) -> Result<(), PagingError> {
        debug_assert_eq!(L::LEVEL, PageLevel::Level0);
        let start_index = entry_index(VirtAddr::from(start), L::LEVEL);
        let count = (end - start) / Self::SMALL.size();
        let mut write = page.lock_to_update(&self.wperms);
        let mut changed = false;
        for index in start_index..start_index + count {
            match write.set_leaf_flags(index, flags) {
                Ok(did_change) => changed |= did_change,
                Err(_) => {
                    let run_end = start + (index - start_index) * Self::SMALL.size();
                    Self::include_l0_footprint(&mut state.footprint, changed, start, run_end);
                    return Err(PagingError::NotMapped);
                }
            }
        }
        let run_end = start + count * Self::SMALL.size();
        Self::include_l0_footprint(&mut state.footprint, changed, start, run_end);
        Ok(())
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

    /// Maps each page in `range` to the next frame. A failure retains the
    /// mapped prefix and reports the remaining number of `PS`-sized pages.
    /// Overlapping writers can change which prefix wins.
    /// Iterator callbacks run without a content guard; a racing writer can
    /// therefore consume frames from a leaf run that loses publication.
    pub fn map_region<PS: PageSize>(
        &self,
        range: PageRangeInclusive<PS>,
        frames: &mut impl Iterator<Item = PhysFrame<PS>>,
        flags: Arch::PTFlags,
    ) -> Result<(), MapRegionError> {
        let ps_pages = range.len();
        self.check_map_region(range, flags)
            .map_err(|error| MapRegionError { error, unmapped_pages: ps_pages })?;
        let mut mapped_ps_pages = 0;
        let root = self.root_view();
        self.map_range_from(&root, range, frames, flags, &mut mapped_ps_pages)
            .map_err(|error| MapRegionError { error, unmapped_pages: ps_pages - mapped_ps_pages })
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
        let root = self.root_view();
        let high_start = VirtAddr::new(LOW_CANONICAL_END).bits();
        let result = if start.bits() < LOW_CANONICAL_END && end.bits() >= high_start {
            self.unmap_range_from(&root, start.bits(), LOW_CANONICAL_END, &mut state)
                .and_then(|()| self.unmap_range_from(&root, high_start, end.bits(), &mut state))
        } else {
            self.unmap_range_from(&root, start.bits(), end.bits(), &mut state)
        };
        if let Err(error) = result {
            let flush = footprint.token::<Arch::TlbFlushTok>();
            if flush.is_pending() {
                flush.flush_tlb_global_sync();
            }
            return Err(error);
        }
        Ok((all_mapped, footprint.token::<Arch::TlbFlushTok>()))
    }

    /// Detaches one bounded batch of empty tables from the batch range.
    fn detach_page_tables_by_range<'id>(
        &mut self,
        batch: &mut DetachBatch<'id, Arch::TlbFlushTok>,
        detached: &mut [Option<DetachedPageTable<'id, Arch, Alloc>>],
    ) -> (usize, bool) {
        let (start, end) = batch.range();
        assert!(start < end, "cleanup range exceeds the root address space");
        let (count, complete) = self.tree.root_mut().detach_range_chunk(
            start,
            end,
            &<Owned::Owned as OwnedIndices>::ROOT_MASK,
            detached,
        );
        if count != 0 {
            batch.record_detachment();
        }
        (count, complete)
    }

    /// Detaches, flushes, and reclaims empty tables intersecting one range.
    ///
    /// Cleanup must proceed as unmap leaves, detach empty tables, flush, then
    /// free the detached tables. Without the flush, stale leaf translations can
    /// still access unmapped and possibly reused data frames, while stale
    /// paging-structure references can walk detached and possibly reused table
    /// pages. A flush between unmap and detach is too early: a later hardware
    /// walk can cache an intermediate-table pointer before its parent entry is
    /// cleared, leaving that cached pointer targeting freed or reused memory.
    ///
    /// `pending` may carry the preceding unmap obligation. Cleanup uses one
    /// flush when all detached tables fit in the bounded gather and flushes
    /// additional chunks only when the gather fills.
    ///
    /// set pending to MayNeedFlush::none() if no prior flush obligation exists.
    pub fn cleanup_page_tables_by_range(
        &mut self,
        start: VirtAddr,
        end: VirtAddr,
        pending: MayNeedFlush<Arch::TlbFlushTok>,
    ) -> usize {
        let span = MaxLevel::LEVEL.size() * PT_ENTRY_COUNT;
        assert!(
            start.bits() < end.bits() && end.bits() <= span,
            "cleanup range exceeds the root address space"
        );
        let mut pending = Some(pending);
        let mut total = 0;
        loop {
            let (count, complete) = with_detach_batch(start, end, |mut batch| {
                batch.include(pending.take().unwrap_or_else(MayNeedFlush::none));
                let mut detached: [Option<_>; DETACHED_TABLE_BATCH_CAPACITY] =
                    core::array::from_fn(|_| None);
                let (count, complete) = self.detach_page_tables_by_range(&mut batch, &mut detached);
                let flushed = batch.flush_tlb_global_sync();
                for tree in detached.into_iter().flatten() {
                    drop(tree.into_staged_after_flush(&flushed));
                }
                (count, complete)
            });
            total += count;
            if complete {
                return total;
            }
        }
    }
}
