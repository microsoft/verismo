//! The page-table page, the frame a walk resolves to, and the edits a single
//! entry can undergo. Entries of a live table are only ever read and written
//! atomically, one word at a time, because the MMU writes them too.
use core::marker::PhantomData;
use core::sync::atomic::AtomicUsize;

use bitflags::Flags;

use super::{PTPagePointer, PTPageTree};
use crate::structs::address::{Address, PhysAddr, VirtAddr, LOW_CANONICAL_END};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::frame::PhysFrame;
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::sizes::{
    entry_index, page_level_for_size, PageSize, Size2MiB, Size4KiB, PT_ENTRY_COUNT,
};
use crate::structs::tlb::{MayNeedFlush, TlbFlush};

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta, P: PagingAllocator> {
    entries: [AtomicUsize; PT_ENTRY_COUNT],
    dummy: PhantomData<(A, P)>,
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    pub(crate) fn set_leaf_flags(entry: &mut PTEntry<A>, flags: A::PTFlags) {
        let mask = A::leaf_flags_mask();
        entry.clear_flags(mask);
        entry.set_flags(flags & mask);
    }

    pub(crate) fn entry_mut(&mut self, index: usize) -> &mut PTEntry<A> {
        let word = self.entries[index].get_mut();
        // SAFETY: PTEntry is transparent over usize; the exclusive page borrow
        // excludes all software and hardware access to this word.
        unsafe { &mut *core::ptr::from_mut(word).cast::<PTEntry<A>>() }
    }

    /// A zeroed table page, and its clean physical address.
    pub fn alloc() -> Result<(*mut Self, PhysAddr), PagingError> {
        let paddr = P::allocate_zeroed_table_page()?;
        let page = P::paddr_to_vaddr(paddr).as_mut_ptr::<Self>();
        Ok((page, paddr))
    }

    /// Discards a wholly unpublished, exclusively owned tree, including its root.
    /// # Safety
    /// Every table page must belong to `P`; no software or hardware may
    /// access the tree, and no child may be shared with another tree.
    pub(crate) unsafe fn free_unpublished(paddr: PhysAddr, level: PageLevel) {
        // SAFETY: every page in this tree is private and exclusively owned.
        let page = unsafe { &mut *P::paddr_to_vaddr(paddr).as_mut_ptr::<Self>() };
        unsafe { page.free_owned_children(level, false) };
        // SAFETY: this private tree's children have been released.
        unsafe { P::deallocate_table_page(paddr) };
    }

    /// The child table `entry` points at, or `None` if it maps a page or maps
    /// nothing. Whether an entry may be followed also depends on its level,
    /// which is the caller's business.
    pub fn child_of(entry: &PTEntry<A>) -> Option<*mut Self> {
        if !entry.present() || entry.huge() {
            return None;
        }
        Some(P::paddr_to_vaddr(PhysAddr::from(entry.address())).as_mut_ptr::<Self>())
    }

    /// The entry at `index` of `page`.
    pub fn entry_ptr(page: *const Self, index: usize) -> *const PTEntry<A> {
        page.cast::<PTEntry<A>>().wrapping_add(index)
    }

    /// The entry at `index` of `page`, for writing.
    pub fn entry_ptr_mut(page: *mut Self, index: usize) -> *mut PTEntry<A> {
        page.cast::<PTEntry<A>>().wrapping_add(index)
    }

    /// Reads entry `index` of `page`.
    ///
    /// # Safety
    /// `page` must be initialized, writable and mapped, with atomic-aligned
    /// entries. Conflicting accesses must be atomic, without ordinary entry references.
    pub unsafe fn read_entry(page: *const Self, index: usize) -> PTEntry<A> {
        assert!(index < PT_ENTRY_COUNT);
        unsafe { PTEntryRef::from_raw(Self::entry_ptr(page, index).cast_mut()) }.load()
    }

    /// # Safety
    /// All descendant tables must be exclusively owned, correctly leveled and
    /// quiesced, with no surviving references; mapped data frames are not freed.
    pub(super) unsafe fn free_owned_children(&mut self, level: PageLevel, clear_entries: bool) {
        for idx in 0..PT_ENTRY_COUNT {
            let entry = *self.entry_mut(idx);
            if entry.is_table(level) {
                let paddr = PhysAddr::from(entry.address());
                // SAFETY: this child is exclusively owned and has no concurrent users.
                let child = unsafe { &mut *P::paddr_to_vaddr(paddr).as_mut_ptr::<Self>() };
                unsafe { child.free_owned_children(level.child().unwrap(), clear_entries) };
                *self.entry_mut(idx) = PTEntry::empty();
                // SAFETY: the child's borrow has ended and its parent no longer links it.
                unsafe { P::deallocate_table_page(paddr) };
                continue;
            }
            if clear_entries {
                *self.entry_mut(idx) = PTEntry::empty();
            }
        }
    }
}

impl<A: ArchPagingMeta, P: DirectMappedAllocator> PTPage<A, P> {
    /// Builds and checks a private direct-mapped tree using ordinary memory
    /// accesses. The owner must publish it before allowing concurrent walkers.
    pub(crate) fn new_direct_mapped(
        level: PageLevel,
        flags: A::PTFlags,
    ) -> Result<PhysAddr, PagingError> {
        let (phys, _) = P::direct_map();
        let start = P::paddr_to_vaddr(phys.start);
        let end = P::paddr_to_vaddr(phys.end);
        let small = PageLevel::Level0;
        let large = PageLevel::Level1;
        assert!(start <= end && start.is_aligned(small.size()) && end.is_aligned(small.size()));
        assert!(phys.start.is_aligned(small.size()));
        let (page, root_pa) = Self::alloc()?;
        // SAFETY: this root has just been allocated and remains unpublished.
        let page = unsafe { &mut *page };
        let parent_flags = A::PTFlags::parent_flags();
        let result = (|| {
            let mut vaddr = start;
            while vaddr < end {
                let paddr = phys.start + (vaddr - start);
                let target = if level >= large
                    && vaddr.is_aligned(large.size())
                    && paddr.is_aligned(large.size())
                    && end - vaddr >= large.size()
                {
                    large
                } else {
                    small
                };
                // SAFETY: all pages remain exclusively owned by this builder.
                match target {
                    PageLevel::Level0 => unsafe {
                        Self::map_unpublished(
                            page,
                            level,
                            Page::<Size4KiB>::from_start_address(vaddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            PhysFrame::<Size4KiB>::from_start_address(paddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            flags,
                            false,
                            parent_flags,
                        )
                    },
                    PageLevel::Level1 => unsafe {
                        Self::map_unpublished(
                            page,
                            level,
                            Page::<Size2MiB>::from_start_address(vaddr)
                                .map_err(|_| PagingError::InvalidAddress)?,
                            PhysFrame::<Size2MiB>::from_start_address(paddr)
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
            // SAFETY: neither the root nor any child has been published.
            unsafe { Self::validate_tree(root_pa, level, |pte_ref| pte_ref.read()) }
        })();
        if let Err(err) = result {
            // SAFETY: no page in this partial tree has escaped construction.
            unsafe { Self::free_unpublished(root_pa, level) };
            return Err(err);
        }
        Ok(root_pa)
    }

    /// Inputs: private tree and mapping; Requires: exclusive unpublished pages; Returns: map status.
    unsafe fn map_unpublished<PS: PageSize>(
        mut page: &mut Self,
        mut level: PageLevel,
        target_page: Page<PS>,
        target_frame: PhysFrame<PS>,
        flags: A::PTFlags,
        shared: bool,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let vaddr = target_page.start_address();
        let depth = level.depth();
        for _ in 0..=depth {
            let entry = page.entry_mut(entry_index(vaddr, level));
            if entry.is_table(level) {
                // SAFETY: this walk only follows private, exclusively owned pages.
                page = unsafe { &mut *Self::child_of(entry).unwrap() };
                level = level.child().unwrap();
            } else if entry.present() {
                return Err(PagingError::EntryAlreadyPresent { level });
            } else {
                return Self::do_map(
                    Mapping::new(level, entry),
                    target_page,
                    target_frame,
                    flags,
                    shared,
                    parent_flags,
                );
            }
        }
        unreachable!("private mapping exceeded the tree depth")
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// # Safety
    /// All followed table pages must stay accessible and correctly leveled.
    /// `read` must use the access protocol of this tree.
    pub(crate) unsafe fn validate_tree(
        root_pa: PhysAddr,
        root_level: PageLevel,
        read: impl Fn(*const PTEntry<A>) -> PTEntry<A> + Copy,
    ) -> Result<(), PagingError> {
        unsafe { Self::validate_page(root_pa, root_level, root_pa, root_level, read) }
    }

    /// Inputs: root and current table; Requires: accessible stable tree; Returns: validation status.
    unsafe fn validate_page(
        root_pa: PhysAddr,
        root_level: PageLevel,
        paddr: PhysAddr,
        level: PageLevel,
        read: impl Fn(*const PTEntry<A>) -> PTEntry<A> + Copy,
    ) -> Result<(), PagingError> {
        let vaddr = P::paddr_to_vaddr(paddr);
        Self::validate_self_mapping(root_pa, root_level, paddr, vaddr, read)?;
        Self::validate_child_tables(root_pa, root_level, level, vaddr, read)
    }

    /// Inputs: root and table addresses; Requires: stable tree; Returns: self-mapping status.
    fn validate_self_mapping(
        root_pa: PhysAddr,
        root_level: PageLevel,
        paddr: PhysAddr,
        vaddr: VirtAddr,
        read: impl Fn(*const PTEntry<A>) -> PTEntry<A> + Copy,
    ) -> Result<(), PagingError> {
        let mut page = P::paddr_to_vaddr(root_pa).as_ptr::<Self>();
        let mut at = root_level;
        for _ in 0..=root_level.depth() {
            let entry = read(Self::entry_ptr(page, entry_index(vaddr, at)));
            if entry.is_table(at) {
                page = Self::child_of(&entry).unwrap();
                at = at.child().unwrap();
                continue;
            }
            let translated =
                (entry.address() & !(at.size() - 1)) + (vaddr.bits() & (at.size() - 1));
            if !entry.is_leaf(at) || translated != paddr.bits() {
                return Err(PagingError::TablePageNotSelfMapped);
            }
            return Ok(());
        }
        unreachable!("self-mapping validation exceeded the tree depth")
    }

    /// Inputs: root and current table; Requires: stable leveled tree; Returns: child validation.
    fn validate_child_tables(
        root_pa: PhysAddr,
        root_level: PageLevel,
        level: PageLevel,
        vaddr: VirtAddr,
        read: impl Fn(*const PTEntry<A>) -> PTEntry<A> + Copy,
    ) -> Result<(), PagingError> {
        let Some(child_level) = level.child() else {
            return Ok(());
        };
        let page = vaddr.as_ptr::<Self>();
        for idx in 0..PT_ENTRY_COUNT {
            let entry = read(Self::entry_ptr(page, idx));
            if !entry.is_table(level) {
                continue;
            }
            unsafe {
                Self::validate_page(
                    root_pa,
                    root_level,
                    PhysAddr::from(entry.address()),
                    child_level,
                    read,
                )
            }?;
        }
        Ok(())
    }
}

/// An entry being edited, and the level it sits at. The entry it borrows is
/// either a staged copy or a page no walker can reach yet, never a live one.
#[derive(Debug)]
pub struct Mapping<'a, A: ArchPagingMeta> {
    pub level: PageLevel,
    pub entry: &'a mut PTEntry<A>,
}

impl<'a, A: ArchPagingMeta> Mapping<'a, A> {
    pub fn new(level: PageLevel, entry: &'a mut PTEntry<A>) -> Self {
        Self { level, entry }
    }
}

/// What a walk found: a physical address, and the size of the page it sits in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Translation<A: ArchPagingMeta> {
    paddr: PhysAddr,
    level: PageLevel,
    dummy: PhantomData<A>,
}

impl<A: ArchPagingMeta> Translation<A> {
    pub fn new(paddr: PhysAddr, level: PageLevel) -> Self {
        Self { paddr, level, dummy: PhantomData }
    }

    /// The level the mapping was found at, which fixes the page size.
    pub fn level(&self) -> PageLevel {
        self.level
    }

    /// The address with the private tag stripped, the shared tag kept.
    pub fn page_frame(&self) -> PhysAddr {
        A::strip_confidentiality_bits(self.paddr)
    }

    /// The clean address: every architectural tag stripped.
    pub fn address(&self) -> PhysAddr {
        A::strip_shared_address_bits(self.page_frame())
    }

    pub fn size(&self) -> usize {
        self.level.size()
    }

    /// The first address of the page this frame falls in.
    pub fn start(&self) -> PhysAddr {
        PhysAddr::from(self.address().bits() & !(self.size() - 1))
    }

    pub fn end(&self) -> PhysAddr {
        self.start() + self.size()
    }
}

/// Restores one temporarily invalidated leaf unless publication disarms it.
struct InvalidatedLeaf<'tree, A: ArchPagingMeta> {
    pte_ref: PTEntryRef<'tree, A>,
    active: bool,
}

impl<'tree, A: ArchPagingMeta> InvalidatedLeaf<'tree, A> {
    /// Inputs: live leaf reference; Requires: excluded software writers; Returns: rollback guard.
    fn new(pte_ref: PTEntryRef<'tree, A>) -> Self {
        pte_ref.fetch_and(!A::PTFlags::present_bit());
        Self { pte_ref, active: true }
    }

    /// Inputs: invalidated guard; Requires: active leaf; Returns: valid-form snapshot.
    fn snapshot(&self) -> PTEntry<A> {
        self.pte_ref.load().with_present()
    }

    /// Inputs: replacement entry; Requires: active guard; Returns: nothing.
    fn publish(&mut self, entry: PTEntry<A>) {
        self.pte_ref.store(entry);
        self.active = false;
    }
}

impl<A: ArchPagingMeta> Drop for InvalidatedLeaf<'_, A> {
    /// Inputs: rollback guard; Requires: pinned entry; Returns: nothing.
    fn drop(&mut self) {
        if self.active {
            // The old encoding stays in place, including history written during the barrier.
            self.pte_ref.fetch_or(A::PTFlags::present_bit());
        }
    }
}

/// An unpublished boundary split prepared for one partially covered huge leaf.
#[cfg_attr(feature = "concurrent", allow(dead_code))]
struct RangeSplit<A: ArchPagingMeta, P: PagingAllocator> {
    base: usize,
    level: PageLevel,
    original: PTEntry<A>,
    tree: PTPageTree<A, P>,
}

const HIGH_CANONICAL_START: usize = VirtAddr::new(LOW_CANONICAL_END).as_usize();

/// Iterates the low and high canonical segments without entering the address hole.
struct CanonicalRangeCursor {
    cursor: usize,
    end: usize,
}

impl CanonicalRangeCursor {
    /// Inputs: canonical bounds; Requires: ordered range; Returns: initialized cursor.
    fn new(start: usize, end: usize) -> Self {
        let cursor = if start == LOW_CANONICAL_END { HIGH_CANONICAL_START } else { start };
        Self { cursor, end }
    }

    /// Inputs: cursor state; Requires: none; Returns: current canonical position.
    fn position(&self) -> usize {
        self.cursor
    }
}

impl Iterator for CanonicalRangeCursor {
    type Item = (usize, usize);

    /// Inputs: cursor state; Requires: canonical bounds; Returns: next valid segment.
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.end {
            return None;
        }
        let seg_start = self.cursor;
        debug_assert!(!(LOW_CANONICAL_END..HIGH_CANONICAL_START).contains(&seg_start));
        let seg_end = if seg_start < LOW_CANONICAL_END && self.end >= HIGH_CANONICAL_START {
            LOW_CANONICAL_END
        } else {
            self.end
        };
        self.cursor = VirtAddr::new(seg_end).as_usize();
        Some((seg_start, seg_end))
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// Inputs: table segment and visitor; Requires: pinned valid tree; Returns: visit status.
    fn sweep_page<'tree, E>(
        page: &PTPagePointer<'tree, A, P>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visit: &mut impl FnMut(
            PhysAddr,
            PTEntryRef<'tree, A>,
            PTEntry<A>,
            PageLevel,
            usize,
            usize,
        ) -> Result<(), E>,
    ) -> Result<(), (usize, E)> {
        debug_assert!(start < end);
        let level = page.level();
        let span = level.size();
        let page_span = span * PT_ENTRY_COUNT;
        let full_page = start & (page_span - 1) == 0 && end - start == page_span;
        let (first_index, last_index) = if full_page {
            (0, PT_ENTRY_COUNT - 1)
        } else {
            (entry_index(VirtAddr::from(start), level), entry_index(VirtAddr::from(end - 1), level))
        };
        debug_assert!(first_index <= last_index);
        let mut cursor = start;
        let mut entry_end = (start & !(span - 1)).saturating_add(span).min(end);
        for index in first_index..=last_index {
            let pte_ref = page.entry(index);
            let entry = pte_ref.load();
            if entry.is_table(level) {
                let child = Self::observed_child(page, entry);
                Self::sweep_page(
                    &child,
                    Some(PhysAddr::from(entry.address())),
                    cursor,
                    entry_end,
                    visit,
                )?;
            } else if let Err(error) = visit(
                page_paddr.unwrap_or_else(|| page.paddr()),
                pte_ref,
                entry,
                level,
                cursor,
                entry_end,
            ) {
                return Err((cursor, error));
            }
            cursor = entry_end;
            entry_end = entry_end.saturating_add(span).min(end);
        }
        Ok(())
    }

    /// Inputs: parent and table entry; Requires: matching observed entry; Returns: child view.
    fn observed_child<'tree>(
        page: &PTPagePointer<'tree, A, P>,
        entry: PTEntry<A>,
    ) -> PTPagePointer<'tree, A, P> {
        match page.child_from_observed(entry) {
            Ok(child) => child,
            Err(_) => unreachable!("observed table entry must resolve as a child"),
        }
    }

    pub(crate) fn sweep_range<'tree, E>(
        root: &PTPagePointer<'tree, A, P>,
        start: usize,
        end: usize,
        visit: &mut impl FnMut(
            PhysAddr,
            PTEntryRef<'tree, A>,
            PTEntry<A>,
            PageLevel,
            usize,
            usize,
        ) -> Result<(), E>,
    ) -> Result<usize, (usize, E)> {
        let mut range = CanonicalRangeCursor::new(start, end);
        for (cursor, segment_end) in &mut range {
            Self::sweep_page(root, None, cursor, segment_end, visit)?;
        }
        Ok(range.position())
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: root and bounds; Requires: nonempty valid range; Returns: split requirement.
    fn range_needs_split(root: &PTPagePointer<'_, A, P>, start: usize, end: usize) -> bool {
        let first = root.walk(VirtAddr::from(start));
        let first_level = first.page.level();
        let first_entry = first.entry().load();
        if first_entry.is_leaf(first_level) && start & (first_level.size() - 1) != 0 {
            return true;
        }

        let (last, segment_end) = if start < LOW_CANONICAL_END && end == HIGH_CANONICAL_START {
            (LOW_CANONICAL_END - 1, LOW_CANONICAL_END)
        } else {
            (end - 1, end)
        };
        let last = root.walk(VirtAddr::from(last));
        let last_level = last.page.level();
        let last_entry = last.entry().load();
        let last_base = segment_end.saturating_sub(1) & !(last_level.size() - 1);
        last_entry.is_leaf(last_level) && last_base.saturating_add(last_level.size()) != segment_end
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: root, range, and flags; Requires: excluded writers; Returns: status and footprint.
    fn update_leaf_flags_in_range(
        root: &PTPagePointer<'_, A, P>,
        start: usize,
        end: usize,
        flags: A::PTFlags,
    ) -> (Result<(), PagingError>, FlushFootprint) {
        let mut footprint = FlushFootprint::default();
        let result =
            Self::sweep_range(root, start, end, &mut |_, pte_ref, observed, level, cursor, _| {
                if !observed.is_leaf(level) {
                    return Err(PagingError::NotMapped);
                }
                let mut current = observed;
                loop {
                    let mut desired = current;
                    Self::set_leaf_flags(&mut desired, flags);
                    if desired.raw() == current.raw() {
                        break;
                    }
                    match pte_ref.compare_exchange(current, desired) {
                        Ok(_) => {
                            footprint.include(VirtAddr::from(cursor), level);
                            break;
                        }
                        Err(latest) => current = latest,
                    }
                }
                Ok(())
            })
            .map(|_| ())
            .map_err(|(_, error)| error);
        (result, footprint)
    }
}

/// Restores PTEs that remain invalidated if a split-range publication is interrupted.
#[cfg_attr(feature = "concurrent", allow(dead_code))]
struct InvalidatedPteRollbackGuard<'view, 'tree, A: ArchPagingMeta, P: PagingAllocator> {
    root: &'view PTPagePointer<'tree, A, P>,
    start: usize,
    end: usize,
}

impl<A: ArchPagingMeta, P: PagingAllocator> Drop for InvalidatedPteRollbackGuard<'_, '_, A, P> {
    /// Inputs: rollback guard; Requires: pinned excluded range; Returns: nothing.
    fn drop(&mut self) {
        let _ = PTPage::<A, P>::sweep_range(
            self.root,
            self.start,
            self.end,
            &mut |_, pte_ref, entry, _, _, _| {
                if !entry.present() {
                    pte_ref.fetch_or(A::PTFlags::present_bit());
                }
                Ok::<(), core::convert::Infallible>(())
            },
        );
    }
}

/// Conservative TLB coverage accumulated from the leaves changed by a range update.
#[derive(Default)]
pub(crate) struct FlushFootprint {
    range: Option<(usize, usize, PageLevel)>,
    all: bool,
}

impl FlushFootprint {
    pub(crate) fn include(&mut self, vaddr: VirtAddr, level: PageLevel) {
        let start = vaddr.bits() & !(level.size() - 1);
        let Some(end) = start.checked_add(level.size()) else {
            self.all = true;
            return;
        };
        if VirtAddr::from(start).bits() != start
            || VirtAddr::from(end).bits() != end
            || (start < LOW_CANONICAL_END && end > LOW_CANONICAL_END)
        {
            self.all = true;
        }
        self.range = Some(match self.range {
            Some((first, last, stride)) => (first.min(start), last.max(end), stride.min(level)),
            None => (start, end, level),
        });
    }

    pub(crate) fn token<T: TlbFlush>(&self) -> MayNeedFlush<T> {
        if self.all {
            MayNeedFlush::all()
        } else if let Some((start, end, level)) = self.range {
            MayNeedFlush::new_range(start.into(), end.into(), level)
        } else {
            MayNeedFlush::none()
        }
    }
}

/// Inputs: flush token and scope; Requires: excluded mapping transition; Returns: nothing.
fn flush_transition<T: TlbFlush>(flush: MayNeedFlush<T>, all_cpus: bool) {
    if all_cpus {
        flush.flush_tlb_global_sync();
    } else {
        flush.flush_tlb_global_percpu();
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// Inputs: mapping and target; Requires: private path; Returns: deepest prepared mapping.
    fn alloc_pte_down<'a, PS: PageSize>(
        map: Mapping<'a, A>,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<Mapping<'a, A>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = target_page.start_address();
        let mut map = map;
        while map.level > target {
            if map.entry.flags().contains(A::PTFlags::PRESENT) {
                return Ok(map);
            }
            let child_level = map.level.child().ok_or(PagingError::InvalidLevel)?;
            let (page, paddr) = Self::alloc()?;
            *map.entry = PTEntry::new_table(A::make_private_address(paddr), parent_flags);
            let index = entry_index(vaddr, child_level);
            // SAFETY: `page` was just allocated and is reachable only through
            // the entry written above, which nothing else holds.
            let page = unsafe { &mut *page };
            let entry = page.entry_mut(index);
            map = Mapping::new(child_level, entry);
        }
        Ok(map)
    }

    /// Inputs: leaf, target, and update; Requires: splittable leaf; Returns: private replacement.
    fn build_split<PS: PageSize, F>(
        entry: PTEntry<A>,
        level: PageLevel,
        target_page: Page<PS>,
        update: F,
    ) -> Result<PTPageTree<A, P>, PagingError>
    where
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = target_page.start_address();
        let child_level = level.child().ok_or(PagingError::InvalidLevel)?;
        let mut tree = PTPageTree::<A, P>::new(child_level)?;
        // SAFETY: this tree is newly allocated and remains wholly unpublished.
        let page = unsafe { tree.page_mut() };
        let target_index = entry_index(vaddr, child_level);
        for idx in 0..PT_ENTRY_COUNT {
            let mut child = entry.split_child(level, idx);
            let mut prepared_subtree = None;
            if idx != target_index {
                *page.entry_mut(idx) = child;
                continue;
            }
            if child_level > target {
                let subtree = Self::build_split(child, child_level, target_page, update)?;
                child = PTEntry::new_table(
                    A::make_private_address(subtree.root_paddr()),
                    A::PTFlags::parent_flags(),
                );
                prepared_subtree = Some(subtree);
            } else {
                child = update(child, child_level);
            }
            *page.entry_mut(idx) = child;
            if let Some(subtree) = prepared_subtree {
                subtree.release();
            }
        }
        Ok(tree)
    }

    /// Inputs: entry and levels; Requires: pinned entry; Returns: validated leaf snapshot.
    fn leaf_for_update(
        pte_ref: PTEntryRef<'_, A>,
        level: PageLevel,
        target: PageLevel,
    ) -> Result<PTEntry<A>, PagingError> {
        if level < target {
            return Err(PagingError::NotLeafEntry);
        }
        let current = pte_ref.load();
        if current.is_leaf(level) {
            Ok(current)
        } else if current.is_table(level) {
            Err(PagingError::NotLeafEntry)
        } else {
            Err(PagingError::NotMapped)
        }
    }

    /// Returns the narrowest flush obligation for one leaf mapping.
    #[inline(always)]
    pub(crate) fn flush_for_leaf(
        vaddr: VirtAddr,
        level: PageLevel,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        if level == PageLevel::Level0 {
            MayNeedFlush::new_small(vaddr)
        } else {
            MayNeedFlush::new(vaddr, level)
        }
    }

    /// Inputs: leaf and replacement; Requires: pinned excluded entry; Returns: pending flush.
    /// # Safety
    /// `pte_ref` must remain allocated at `level`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Local flushing requires no stale remote translations or migration.
    unsafe fn replace_leaf_mapping<F>(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
        level: PageLevel,
        vaddr: VirtAddr,
        update: F,
        all_cpus: bool,
    ) -> MayNeedFlush<A::TlbFlushTok>
    where
        F: Fn(PTEntry<A>) -> PTEntry<A>,
    {
        loop {
            let desired = update(current);
            if desired.raw() == current.raw() {
                return MayNeedFlush::none();
            }
            let flush = Self::flush_for_leaf(vaddr, level);
            if A::requires_break_before_make(current.raw(), desired.raw(), level) {
                let mut invalidated = InvalidatedLeaf::new(pte_ref);
                flush_transition(flush, all_cpus);
                let latest = invalidated.snapshot();
                invalidated.publish(update(latest));
                return MayNeedFlush::none();
            }
            match pte_ref.compare_exchange(current, desired) {
                Ok(_) => return flush,
                Err(latest) => current = latest,
            }
        }
    }

    /// Inputs: leaf, target, update, and scope; Requires: pinned excluded entry; Returns: flush.
    /// # Safety
    /// `pte_ref` must remain allocated at `level`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Exclusion must outlive unwinding. Local flushing also requires no stale
    /// remote translations and no migration through the entire transition.
    unsafe fn publish_split<PS: PageSize, F>(
        pte_ref: PTEntryRef<'_, A>,
        level: PageLevel,
        target_page: Page<PS>,
        mut current: PTEntry<A>,
        update: F,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
    where
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        let vaddr = target_page.start_address();
        let mut tree = Self::build_split(current, level, target_page, update)?;
        let root = tree.root_paddr();
        let replacement =
            PTEntry::new_table(A::make_private_address(root), A::PTFlags::parent_flags());
        let flush = MayNeedFlush::<A::TlbFlushTok>::new(vaddr, level);
        if A::requires_break_before_make(current.raw(), replacement.raw(), level) {
            let mut invalidated = InvalidatedLeaf::new(pte_ref);
            flush_transition(flush, all_cpus);
            // SAFETY: the subtree remains private during the architecture's BBM barrier.
            unsafe {
                Self::refresh_split(
                    tree.page_mut(),
                    invalidated.snapshot(),
                    level,
                    target_page,
                    update,
                )
            };
            invalidated.publish(replacement);
            tree.release();
            return Ok(MayNeedFlush::none());
        }
        loop {
            match pte_ref.compare_exchange(current, replacement) {
                Ok(_) => break,
                Err(latest) => {
                    current = latest;
                    // SAFETY: the subtree is private until the compare-exchange publishes it.
                    unsafe {
                        Self::refresh_split(tree.page_mut(), current, level, target_page, update)
                    };
                }
            }
        }
        tree.release();
        flush_transition(flush, all_cpus);
        Ok(MayNeedFlush::none())
    }

    /// # Safety
    /// `pte_ref` must stay pinned and software writers must remain excluded.
    pub(crate) unsafe fn split_leaf<PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        level: PageLevel,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let current = Self::leaf_for_update(pte_ref, level, target)?;
        if level == target {
            return Ok(MayNeedFlush::none());
        }
        unsafe { Self::publish_split(pte_ref, level, page, current, |entry, _| entry, all_cpus) }
    }

    /// # Safety
    /// `pte_ref` must stay pinned and software writers must remain excluded.
    pub(crate) unsafe fn update_encryption_leaf<PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        level: PageLevel,
        page: Page<PS>,
        shared: bool,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        let current = Self::leaf_for_update(pte_ref, level, target)?;
        let update = |mut entry: PTEntry<A>, _| {
            if shared {
                entry.make_shared();
            } else {
                entry.make_private();
            }
            entry
        };
        if level > target {
            return unsafe { Self::publish_split(pte_ref, level, page, current, update, all_cpus) };
        }

        Ok(unsafe {
            Self::replace_leaf_mapping(
                pte_ref,
                current,
                level,
                vaddr,
                |entry| update(entry, level),
                all_cpus,
            )
        })
    }

    /// # Safety
    /// `pte_ref` must stay pinned and software writers must remain excluded.
    pub(crate) unsafe fn update_leaf_flags_at<PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        level: PageLevel,
        page: Page<PS>,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let vaddr = page.start_address();
        let current = Self::leaf_for_update(pte_ref, level, target)?;
        let flags = A::filter_flags(flags);
        if level > target {
            return unsafe {
                Self::publish_split(
                    pte_ref,
                    level,
                    page,
                    current,
                    |mut entry, _level| {
                        Self::set_leaf_flags(&mut entry, flags);
                        entry
                    },
                    all_cpus,
                )
            };
        }
        // SAFETY: the caller excludes writers and `current` is the locked leaf snapshot.
        Ok(unsafe { Self::update_leaf_flags_in_place(pte_ref, current, level, vaddr, flags) })
    }

    /// # Safety
    /// `pte_ref` must remain allocated at `level` with software writers excluded,
    /// and `current` must be its locked leaf observation.
    #[inline(always)]
    pub(crate) unsafe fn update_leaf_flags_in_place(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
        level: PageLevel,
        vaddr: VirtAddr,
        flags: A::PTFlags,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        loop {
            let mut desired = current;
            Self::set_leaf_flags(&mut desired, flags);
            if desired.raw() == current.raw() {
                return MayNeedFlush::none();
            }
            // Permission replacement must preserve A/D that raced with this snapshot.
            match pte_ref.compare_exchange(current, desired) {
                Ok(_) => return Self::flush_for_leaf(vaddr, level),
                Err(entry) => current = entry,
            }
        }
    }

    /// Inputs: private tree and leaf snapshot; Requires: matching split shape; Returns: nothing.
    unsafe fn refresh_split<PS: PageSize, F>(
        page: &mut Self,
        entry: PTEntry<A>,
        level: PageLevel,
        target_page: Page<PS>,
        update: F,
    ) where
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        let target = page_level_for_size::<PS>().unwrap();
        let vaddr = target_page.start_address();
        let child_level = level.child().unwrap();
        let target_index = entry_index(vaddr, child_level);
        for idx in 0..PT_ENTRY_COUNT {
            let pte_ref = page.entry_mut(idx);
            let mut child = entry.split_child(level, idx);
            if idx != target_index {
                *pte_ref = child;
                continue;
            }
            if child_level > target {
                let table = *pte_ref;
                let child_page = unsafe {
                    &mut *P::paddr_to_vaddr(PhysAddr::from(table.address())).as_mut_ptr::<Self>()
                };
                unsafe { Self::refresh_split(child_page, child, child_level, target_page, update) };
                child = table;
            } else {
                child = update(child, child_level);
            }
            *pte_ref = child;
        }
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: leaf, local range, and flags; Requires: splittable leaf; Returns: private subtree.
    fn build_range_split(
        entry: PTEntry<A>,
        level: PageLevel,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) -> Result<PTPageTree<A, P>, PagingError> {
        let child_level = level.child().ok_or(PagingError::InvalidLevel)?;
        let mut tree = PTPageTree::new(child_level)?;
        // SAFETY: this tree retains every initialized, unpublished table page.
        let page = unsafe { tree.page_mut() };
        for idx in 0..PT_ENTRY_COUNT {
            let mut child = entry.split_child(level, idx);
            let offset = idx * child_level.size();
            let first = from.saturating_sub(offset).min(child_level.size());
            let last = to.saturating_sub(offset).min(child_level.size());
            let mut subtree = None;
            if first < last && !child_level.is_leaf() && (first != 0 || last != child_level.size())
            {
                subtree = Some(Self::build_range_split(child, child_level, first, last, flags)?);
                child = PTEntry::new_table(
                    A::make_private_address(subtree.as_ref().unwrap().root_paddr()),
                    A::PTFlags::parent_flags(),
                );
            } else if first < last {
                Self::set_leaf_flags(&mut child, flags);
            }
            *page.entry_mut(idx) = child;
            if let Some(subtree) = subtree {
                subtree.release();
            }
        }
        Ok(tree)
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: private tree and leaf snapshot; Requires: matching range split; Returns: nothing.
    unsafe fn refresh_range_split(
        page: &mut Self,
        entry: PTEntry<A>,
        level: PageLevel,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) {
        let child_level = level.child().unwrap();
        for idx in 0..PT_ENTRY_COUNT {
            let pte_ref = page.entry_mut(idx);
            let table = *pte_ref;
            let mut child = entry.split_child(level, idx);
            let offset = idx * child_level.size();
            let first = from.saturating_sub(offset).min(child_level.size());
            let last = to.saturating_sub(offset).min(child_level.size());
            if table.is_table(child_level) {
                let child_page = unsafe {
                    &mut *P::paddr_to_vaddr(PhysAddr::from(table.address())).as_mut_ptr::<Self>()
                };
                unsafe {
                    Self::refresh_range_split(child_page, child, child_level, first, last, flags)
                };
                *pte_ref = table;
                continue;
            }
            if first < last {
                Self::set_leaf_flags(&mut child, flags);
            }
            *pte_ref = child;
        }
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: entry, snapshot, and flags; Requires: pinned leaf; Returns: nothing.
    fn update_flags_with_cas(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
        flags: A::PTFlags,
    ) {
        loop {
            let mut desired = current;
            Self::set_leaf_flags(&mut desired, flags);
            if desired.raw() == current.raw() {
                return;
            }
            match pte_ref.compare_exchange(current, desired) {
                Ok(_) => return,
                Err(latest) => current = latest,
            }
        }
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: entry and split state; Requires: pinned excluded entry; Returns: nothing.
    unsafe fn publish_range_split_with_cas(
        pte_ref: PTEntryRef<'_, A>,
        split: &mut RangeSplit<A, P>,
        mut current: PTEntry<A>,
        level: PageLevel,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) {
        let replacement = PTEntry::new_table(
            A::make_private_address(split.tree.root_paddr()),
            A::PTFlags::parent_flags(),
        );
        if current.raw() != split.original.raw() {
            unsafe {
                Self::refresh_range_split(split.tree.page_mut(), current, level, from, to, flags)
            };
        }
        loop {
            match pte_ref.compare_exchange(current, replacement) {
                Ok(_) => return,
                Err(latest) => {
                    current = latest;
                    unsafe {
                        Self::refresh_range_split(
                            split.tree.page_mut(),
                            current,
                            level,
                            from,
                            to,
                            flags,
                        )
                    };
                }
            }
        }
    }

    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    /// Inputs: segment and range bounds; Requires: boundary segment; Returns: boundary index.
    fn range_boundary_index(
        cursor: usize,
        next: usize,
        range_start: usize,
        range_end: usize,
    ) -> Result<usize, PagingError> {
        if cursor == range_start {
            return Ok(0);
        }
        if next == range_end {
            return Ok(1);
        }
        Err(PagingError::InvalidRange)
    }

    /// Updates the valid prefix with one barrier if either boundary needs a split.
    /// Allocation failure leaves the entire original leaf being prepared unchanged;
    /// earlier original leaves may still be updated.
    ///
    /// # Safety
    /// The well-formed tree must stay pinned, and all software writers must be
    /// excluded throughout the batch and its unwind. Only hardware A/D writes
    /// may race. Flags and range alignment must already be checked. Local scope
    /// requires no stale remote translations or migration during the transition.
    #[cfg_attr(feature = "concurrent", allow(dead_code))]
    pub(crate) unsafe fn update_leaf_flags_range(
        root: PTPagePointer<'_, A, P>,
        start: VirtAddr,
        end: VirtAddr,
        flags: A::PTFlags,
        all_cpus: bool,
    ) -> (Result<(), PagingError>, MayNeedFlush<A::TlbFlushTok>) {
        let flags = A::filter_flags(flags);
        let range_start = start.bits();
        let range_end = end.bits();

        // A range with no partial huge leaf is completed by one forward sweep.
        if !Self::range_needs_split(&root, range_start, range_end) {
            let (result, deferred) =
                Self::update_leaf_flags_in_range(&root, range_start, range_end, flags);
            return (result, deferred.token());
        }

        let mut boundary_splits: [Option<RangeSplit<A, P>>; 2] = [None, None];
        let mut footprint = FlushFootprint::default();
        let mut result = Ok(());

        // Prepare the first and last partial huge leaves before changing the live tree.
        let planning_result = Self::sweep_range(
            &root,
            range_start,
            range_end,
            &mut |_, _, entry, level, cursor, next| {
                if !entry.is_leaf(level) {
                    return Err(PagingError::NotMapped);
                }
                let base = cursor & !(level.size() - 1);
                let partial = cursor != base || next - cursor != level.size();
                if partial {
                    let boundary =
                        Self::range_boundary_index(cursor, next, range_start, range_end)?;
                    let tree =
                        Self::build_range_split(entry, level, cursor - base, next - base, flags)?;
                    boundary_splits[boundary] =
                        Some(RangeSplit { base, level, original: entry, tree });
                }
                footprint.include(VirtAddr::from(cursor), level);
                Ok(())
            },
        );
        let prefix_end = match planning_result {
            Ok(prefix_end) => prefix_end,
            Err((prefix_end, error)) => {
                result = Err(error);
                prefix_end
            }
        };

        // A predicted boundary beyond an invalid prefix may leave no split to publish.
        if boundary_splits.iter().all(Option::is_none) {
            let (updated, deferred) =
                Self::update_leaf_flags_in_range(&root, range_start, prefix_end, flags);
            debug_assert!(updated.is_ok());
            return (result, deferred.token());
        }

        let requires_bbm = boundary_splits.iter().flatten().any(|split| {
            let replacement = PTEntry::<A>::new_table(
                A::make_private_address(split.tree.root_paddr()),
                A::PTFlags::parent_flags(),
            );
            A::requires_break_before_make(split.original.raw(), replacement.raw(), split.level)
        });

        if !requires_bbm {
            let publication = Self::sweep_range(
                &root,
                range_start,
                prefix_end,
                &mut |_, pte_ref, entry, level, cursor, next| {
                    let base = cursor & !(level.size() - 1);
                    if let Some(index) = boundary_splits
                        .iter()
                        .position(|split| matches!(split, Some(split) if split.base == base))
                    {
                        let split = boundary_splits[index].as_mut().unwrap();
                        unsafe {
                            Self::publish_range_split_with_cas(
                                pte_ref,
                                split,
                                entry,
                                level,
                                cursor - base,
                                next - base,
                                flags,
                            )
                        };
                        boundary_splits[index].take().unwrap().tree.release();
                    } else {
                        Self::update_flags_with_cas(pte_ref, entry, flags);
                    }
                    Ok::<(), core::convert::Infallible>(())
                },
            );
            debug_assert!(publication.is_ok());
            flush_transition(footprint.token::<A::TlbFlushTok>(), all_cpus);
            return (result, MayNeedFlush::none());
        }

        // Only descriptors undergoing an architecture-required transition are broken.
        let flush = footprint.token::<A::TlbFlushTok>();
        // Declared after split plans so rollback restores mappings before freeing private pages.
        let mut invalidated = InvalidatedPteRollbackGuard::<A, P> {
            root: &root,
            start: range_start,
            end: range_start,
        };
        let invalidation = Self::sweep_range(
            &root,
            range_start,
            prefix_end,
            &mut |_, pte_ref, entry, level, cursor, next| {
                let base = cursor & !(level.size() - 1);
                if boundary_splits
                    .iter()
                    .any(|split| matches!(split, Some(split) if split.base == base))
                {
                    pte_ref.fetch_and(!A::PTFlags::present_bit());
                } else {
                    Self::update_flags_with_cas(pte_ref, entry, flags);
                }
                invalidated.end = next;
                Ok::<(), core::convert::Infallible>(())
            },
        );
        debug_assert!(invalidation.is_ok());
        flush_transition(flush, all_cpus);

        // Publish prepared boundary trees and restore updated complete leaves.
        let publication = Self::sweep_range(
            &root,
            invalidated.start,
            prefix_end,
            &mut |_, pte_ref, entry, level, cursor, next| {
                invalidated.start = cursor;
                let base = cursor & !(level.size() - 1);
                let old = entry.with_present();
                if let Some(index) = boundary_splits
                    .iter()
                    .position(|plan| matches!(plan, Some(plan) if plan.base == base))
                {
                    let plan = boundary_splits[index].as_mut().unwrap();
                    let root = plan.tree.root_paddr();
                    // SAFETY: the barrier has completed; these pages are still wholly private.
                    unsafe {
                        Self::refresh_range_split(
                            plan.tree.page_mut(),
                            old,
                            level,
                            cursor - base,
                            next - base,
                            flags,
                        )
                    };
                    pte_ref.store(PTEntry::new_table(
                        A::make_private_address(root),
                        A::PTFlags::parent_flags(),
                    ));
                    boundary_splits[index].take().unwrap().tree.release();
                }
                invalidated.start = next;
                Ok::<(), core::convert::Infallible>(())
            },
        );
        debug_assert!(publication.is_ok());
        (result, MayNeedFlush::none())
    }

    /// Maps `page` to `frame`, building the tables above it. The
    /// walk that got here reports an entry already present, so what this finds
    /// is either empty or a table it has to descend.
    pub(crate) fn do_map<PS: PageSize>(
        map: Mapping<'_, A>,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: A::PTFlags,
        shared: bool,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let target = page_level_for_size::<PS>().ok_or(PagingError::InvalidLevel)?;
        let paddr = frame.start_address();
        let map = Self::alloc_pte_down(map, page, A::filter_flags(parent_flags))?;
        if map.level != target {
            return Err(PagingError::AllocFrame);
        }
        let addr =
            if shared { A::make_shared_address(paddr) } else { A::make_private_address(paddr) };
        let flags = A::filter_flags(flags);
        let flags = if target.is_leaf() { flags } else { flags.with(A::PTFlags::HUGE) };
        *map.entry = PTEntry::new(addr, flags);
        Ok(())
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
#[path = "../../../tests/unit/ptpage.rs"]
mod view_tests;
