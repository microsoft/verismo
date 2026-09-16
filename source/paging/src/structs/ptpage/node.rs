//! The page-table page, the frame a walk resolves to, and the edits a single
//! entry can undergo. Entries of a live table are only ever read and written
//! atomically, one word at a time, because the MMU writes them too.
use core::marker::PhantomData;
#[cfg(any(feature = "use_ad", feature = "concurrent"))]
use core::sync::atomic::AtomicUsize;

use bitflags::Flags;

use super::{PTPagePointer, PTPageTree};
use crate::structs::address::{Address, PhysAddr, VirtAddr, LOW_CANONICAL_END};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::sizes::{entry_index, ENTRY_COUNT};
use crate::structs::tlb::{MayNeedFlush, TlbFlush};

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta, P: PagingAllocator> {
    #[cfg(any(feature = "use_ad", feature = "concurrent"))]
    entries: [AtomicUsize; ENTRY_COUNT],
    #[cfg(not(any(feature = "use_ad", feature = "concurrent")))]
    entries: [PTEntry<A>; ENTRY_COUNT],
    dummy: PhantomData<(A, P)>,
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// How many entries a table page holds: one page of the smallest size this
    /// build maps, filled with entries.
    pub const COUNT: usize = ENTRY_COUNT;

    pub(crate) fn entry_mut(&mut self, index: usize) -> &mut PTEntry<A> {
        #[cfg(any(feature = "use_ad", feature = "concurrent"))]
        {
            let word = self.entries[index].get_mut();
            // SAFETY: PTEntry is transparent over usize; the exclusive page borrow
            // excludes all software and hardware access to this word.
            unsafe { &mut *core::ptr::from_mut(word).cast::<PTEntry<A>>() }
        }
        #[cfg(not(any(feature = "use_ad", feature = "concurrent")))]
        {
            &mut self.entries[index]
        }
    }

    /// A zeroed table page, and its clean physical address.
    pub fn alloc() -> Result<(*mut Self, PhysAddr), PagingError> {
        let paddr = P::allocate_table_page()?;
        let page = P::paddr_to_vaddr(paddr).as_mut_ptr::<Self>();
        // SAFETY: the allocator supplies an exclusive, writable frame; no entry is live yet.
        unsafe { page.write_bytes(0, 1) };
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
        assert!(index < Self::COUNT);
        unsafe { PTEntryRef::from_raw(Self::entry_ptr(page, index).cast_mut()) }.load()
    }

    /// # Safety
    /// All descendant tables must be exclusively owned, correctly leveled and
    /// quiesced, with no surviving references; mapped data frames are not freed.
    pub(super) unsafe fn free_owned_children(&mut self, level: PageLevel, clear_entries: bool) {
        for idx in 0..Self::COUNT {
            let entry = *self.entry_mut(idx);
            if !entry.is_table(level) {
                if clear_entries {
                    *self.entry_mut(idx) = PTEntry::empty();
                }
                continue;
            }
            let paddr = PhysAddr::from(entry.address());
            // SAFETY: this child is exclusively owned and has no concurrent users.
            let child = unsafe { &mut *P::paddr_to_vaddr(paddr).as_mut_ptr::<Self>() };
            unsafe { child.free_owned_children(level.child().unwrap(), clear_entries) };
            *self.entry_mut(idx) = PTEntry::empty();
            // SAFETY: the child's borrow has ended and its parent no longer links it.
            unsafe { P::deallocate_table_page(paddr) };
        }
    }

    /// # Safety
    /// The validated tree must be acyclic and correctly leveled. Every table,
    /// including shared subtrees, must exclude all software and hardware access
    /// and aliases for this traversal. Flush stale translations before resuming.
    #[cfg(not(feature = "use_ad"))]
    pub(crate) unsafe fn normalize_ad_tree(root_pa: PhysAddr, root_level: PageLevel) {
        // SAFETY: the caller quiesces every reachable page and excludes aliases.
        let page = unsafe { &mut *P::paddr_to_vaddr(root_pa).as_mut_ptr::<Self>() };
        for index in 0..Self::COUNT {
            let entry = page.entry_mut(index);
            if !entry.present() {
                continue;
            }
            *entry = entry.for_publication();
            if entry.is_table(root_level) {
                unsafe {
                    Self::normalize_ad_tree(
                        PhysAddr::from(entry.address()),
                        root_level.child().unwrap(),
                    )
                };
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
        let spec = MapSpec { flags, shared: false, parent_flags: A::PTFlags::parent_flags() };
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
                unsafe { Self::map_unpublished(page, level, vaddr, paddr, target, spec) }?;
                vaddr = vaddr + target.size();
            }
            // SAFETY: neither the root nor any child has been published.
            unsafe { Self::validate_tree(root_pa, level, |slot| slot.read()) }
        })();
        if let Err(err) = result {
            // SAFETY: no page in this partial tree has escaped construction.
            unsafe { Self::free_unpublished(root_pa, level) };
            return Err(err);
        }
        Ok(root_pa)
    }

    unsafe fn map_unpublished(
        mut page: &mut Self,
        mut level: PageLevel,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        spec: MapSpec<A>,
    ) -> Result<(), PagingError> {
        loop {
            let entry = page.entry_mut(entry_index(vaddr, level));
            if entry.is_table(level) {
                // SAFETY: this walk only follows private, exclusively owned pages.
                page = unsafe { &mut *Self::child_of(entry).unwrap() };
                level = level.child().unwrap();
            } else if entry.present() {
                return Err(PagingError::EntryAlreadyPresent {
                    frame: PhysAddr::from(
                        (entry.address() & !(level.size() - 1))
                            + (vaddr.bits() & (level.size() - 1)),
                    ),
                    level,
                });
            } else {
                return Self::do_map(Mapping::new(level, entry), vaddr, paddr, target, spec);
            }
        }
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

    unsafe fn validate_page(
        root_pa: PhysAddr,
        root_level: PageLevel,
        paddr: PhysAddr,
        level: PageLevel,
        read: impl Fn(*const PTEntry<A>) -> PTEntry<A> + Copy,
    ) -> Result<(), PagingError> {
        let vaddr = P::paddr_to_vaddr(paddr);
        let mut page = P::paddr_to_vaddr(root_pa).as_ptr::<Self>();
        let mut at = root_level;
        loop {
            let entry = read(Self::entry_ptr(page, entry_index(vaddr, at)));
            if entry.is_table(at) {
                page = Self::child_of(&entry).unwrap();
                at = at.child().unwrap();
            } else {
                let translated =
                    (entry.address() & !(at.size() - 1)) + (vaddr.bits() & (at.size() - 1));
                if !entry.is_leaf(at) || translated != paddr.bits() {
                    return Err(PagingError::TablePageNotSelfMapped);
                }
                break;
            }
        }
        if let Some(child_level) = level.child() {
            let page = vaddr.as_ptr::<Self>();
            for idx in 0..Self::COUNT {
                let entry = read(Self::entry_ptr(page, idx));
                if entry.is_table(level) {
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
            }
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

/// What a mapping is made of: the flags of the leaf, whether the frame is
/// shared, and the flags of any table created to reach it.
#[derive(Clone, Copy, Debug)]
pub struct MapSpec<A: ArchPagingMeta> {
    pub flags: A::PTFlags,
    pub shared: bool,
    pub parent_flags: A::PTFlags,
}

/// One leaf-level transformation performed by the shared edit engine.
#[derive(Clone, Copy)]
pub(crate) enum LeafUpdate<A: ArchPagingMeta> {
    Split,
    UpdateEncryption(bool),
    Protect(A::PTFlags),
}

/// Restores one temporarily invalidated leaf unless publication disarms it.
struct InvalidatedLeaf<'tree, A: ArchPagingMeta> {
    slot: PTEntryRef<'tree, A>,
    active: bool,
}

impl<'tree, A: ArchPagingMeta> InvalidatedLeaf<'tree, A> {
    fn new(slot: PTEntryRef<'tree, A>) -> Self {
        slot.fetch_and(!A::PTFlags::present_bit());
        Self { slot, active: true }
    }

    fn snapshot(&self) -> PTEntry<A> {
        PTEntry::from_bits(self.slot.load().raw() | A::PTFlags::present_bit())
    }

    fn publish(&mut self, entry: PTEntry<A>) {
        self.slot.store(entry);
        self.active = false;
    }
}

impl<A: ArchPagingMeta> Drop for InvalidatedLeaf<'_, A> {
    fn drop(&mut self) {
        if self.active {
            // The old encoding stays in place, including history written during the barrier.
            self.slot.fetch_or(A::PTFlags::present_bit());
        }
    }
}

/// An unpublished boundary split prepared for one partially covered huge leaf.
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
    fn new(start: usize, end: usize) -> Self {
        Self { cursor: start, end }
    }

    fn current(&mut self) -> Option<(usize, usize)> {
        if self.cursor == LOW_CANONICAL_END {
            self.cursor = HIGH_CANONICAL_START;
        }
        if self.cursor >= self.end {
            return None;
        }
        debug_assert!(self.cursor < LOW_CANONICAL_END || self.cursor >= HIGH_CANONICAL_START);
        let segment_end = if self.cursor < LOW_CANONICAL_END && self.end >= HIGH_CANONICAL_START {
            LOW_CANONICAL_END
        } else {
            self.end
        };
        Some((self.cursor, segment_end))
    }

    fn advance(&mut self, next: usize) {
        self.cursor = next;
    }

    fn position(&self) -> usize {
        self.cursor
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    fn sweep_page<'tree, E>(
        page: &PTPagePointer<'tree, A, P>,
        start: usize,
        end: usize,
        visit: &mut impl FnMut(
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
        let page_span = span * Self::COUNT;
        let full_page = start & (page_span - 1) == 0 && end - start == page_span;
        let (first_index, last_index) = if full_page {
            (0, Self::COUNT - 1)
        } else {
            (entry_index(VirtAddr::from(start), level), entry_index(VirtAddr::from(end - 1), level))
        };
        debug_assert!(first_index <= last_index);
        let mut cursor = start;
        let mut slot_end = (start & !(span - 1)).saturating_add(span).min(end);
        for index in first_index..=last_index {
            let slot = page.entry(index);
            let entry = slot.load();
            if entry.is_table(level) {
                let child = match page.child_from_observed(entry) {
                    Ok(child) => child,
                    Err(_) => unreachable!("observed table entry must resolve as a child"),
                };
                Self::sweep_page(&child, cursor, slot_end, visit)?;
            } else if let Err(error) = visit(slot, entry, level, cursor, slot_end) {
                return Err((cursor, error));
            }
            cursor = slot_end;
            slot_end = slot_end.saturating_add(span).min(end);
        }
        Ok(())
    }

    fn sweep_range<'tree, E>(
        root: &PTPagePointer<'tree, A, P>,
        start: usize,
        end: usize,
        visit: &mut impl FnMut(
            PTEntryRef<'tree, A>,
            PTEntry<A>,
            PageLevel,
            usize,
            usize,
        ) -> Result<(), E>,
    ) -> Result<usize, (usize, E)> {
        let mut range = CanonicalRangeCursor::new(start, end);
        while let Some((cursor, segment_end)) = range.current() {
            Self::sweep_page(root, cursor, segment_end, visit)?;
            range.advance(segment_end);
        }
        Ok(range.position())
    }

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

    fn protect_leaf_range(
        root: &PTPagePointer<'_, A, P>,
        start: usize,
        end: usize,
        flags: A::PTFlags,
    ) -> (Result<(), PagingError>, FlushFootprint) {
        let mut footprint = FlushFootprint::default();
        let result =
            Self::sweep_range(root, start, end, &mut |slot, observed, level, cursor, _| {
                if !observed.is_leaf(level) {
                    return Err(PagingError::NotMapped);
                }
                let mut current = observed;
                loop {
                    let desired = current.with_leaf_flags(level, flags);
                    if desired.raw() == current.raw() {
                        break;
                    }
                    match slot.compare_exchange(current, desired) {
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
struct InvalidatedPteRollbackGuard<'view, 'tree, A: ArchPagingMeta, P: PagingAllocator> {
    root: &'view PTPagePointer<'tree, A, P>,
    start: usize,
    end: usize,
}

impl<A: ArchPagingMeta, P: PagingAllocator> Drop for InvalidatedPteRollbackGuard<'_, '_, A, P> {
    fn drop(&mut self) {
        let _ = PTPage::<A, P>::sweep_range(
            self.root,
            self.start,
            self.end,
            &mut |slot, entry, _, _, _| {
                if !entry.present() {
                    slot.fetch_or(A::PTFlags::present_bit());
                }
                Ok::<(), core::convert::Infallible>(())
            },
        );
    }
}

/// Conservative TLB coverage accumulated from the leaves changed by a range update.
#[derive(Default)]
struct FlushFootprint {
    range: Option<(usize, usize, PageLevel)>,
    all: bool,
}

impl FlushFootprint {
    fn include(&mut self, vaddr: VirtAddr, level: PageLevel) {
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

    fn token<T: TlbFlush>(&self) -> MayNeedFlush<T> {
        if self.all {
            MayNeedFlush::all()
        } else if let Some((start, end, level)) = self.range {
            MayNeedFlush::new_range(start.into(), end.into(), level)
        } else {
            MayNeedFlush::none()
        }
    }
}

fn flush_transition<T: TlbFlush>(flush: MayNeedFlush<T>, all_cpus: bool) {
    if all_cpus {
        flush.flush_tlb_global_sync();
    } else {
        flush.flush_tlb_global_percpu();
    }
}

impl<A: ArchPagingMeta> LeafUpdate<A> {
    pub(crate) fn apply(self, mut entry: PTEntry<A>, level: PageLevel) -> PTEntry<A> {
        match self {
            Self::Split => entry,
            Self::UpdateEncryption(true) => {
                entry.make_shared();
                entry
            }
            Self::UpdateEncryption(false) => {
                entry.make_private();
                entry
            }
            Self::Protect(flags) => entry.with_leaf_flags(level, A::filter_flags(flags)),
        }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// Builds tables from `map` down towards `target`, stopping at a present
    /// entry and propagating allocation failures. Every page it creates is filled
    /// before it is linked, so no walker sees a half-built table.
    fn alloc_pte_down<'a>(
        map: Mapping<'a, A>,
        vaddr: VirtAddr,
        target: PageLevel,
        parent_flags: A::PTFlags,
    ) -> Result<Mapping<'a, A>, PagingError> {
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

    /// Prepares a complete split path without exposing any of its pages.
    /// Returns ownership of the privately initialized replacement.
    pub(crate) fn build_split(
        entry: PTEntry<A>,
        level: PageLevel,
        vaddr: VirtAddr,
        target: PageLevel,
        update: LeafUpdate<A>,
    ) -> Result<PTPageTree<A, P>, PagingError> {
        let child_level = level.child().ok_or(PagingError::InvalidLevel)?;
        let mut tree = PTPageTree::<A, P>::new(child_level)?;
        // SAFETY: this tree is newly allocated and remains wholly unpublished.
        let page = unsafe { tree.page_mut() };
        for idx in 0..Self::COUNT {
            let mut child = entry.split_child(level, idx);
            let mut prepared_subtree = None;
            if idx == entry_index(vaddr, child_level) {
                if child_level > target {
                    let subtree = Self::build_split(child, child_level, vaddr, target, update)?;
                    child = PTEntry::new_table(
                        A::make_private_address(subtree.root_paddr()),
                        A::PTFlags::parent_flags(),
                    );
                    prepared_subtree = Some(subtree);
                } else {
                    child = update.apply(child, child_level);
                }
            }
            *page.entry_mut(idx) = child.for_publication();
            if let Some(subtree) = prepared_subtree {
                subtree.release();
            }
        }
        Ok(tree)
    }

    fn prepare_update(
        entry: PTEntry<A>,
        level: PageLevel,
        vaddr: VirtAddr,
        target: PageLevel,
        update: LeafUpdate<A>,
    ) -> Result<PTEntry<A>, PagingError> {
        if level > target {
            let tree = Self::build_split(entry, level, vaddr, target, update)?;
            let desired = PTEntry::new_table(
                A::make_private_address(tree.root_paddr()),
                A::PTFlags::parent_flags(),
            );
            tree.release();
            Ok(desired)
        } else {
            Ok(update.apply(entry, level).for_publication())
        }
    }

    /// Changes one live leaf using the architecture's required transition order.
    /// # Safety
    /// `slot` must remain allocated at `level`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Exclusion must outlive unwinding. Local flushing also requires no stale
    /// remote translations and no migration through the entire transition.
    pub(crate) unsafe fn edit_leaf(
        slot: PTEntryRef<'_, A>,
        level: PageLevel,
        vaddr: VirtAddr,
        target: PageLevel,
        update: LeafUpdate<A>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        if level < target {
            return Err(PagingError::NotLeafEntry);
        }
        let mut current = slot.load();
        if !current.is_leaf(level) {
            return Err(if current.is_table(level) {
                PagingError::NotLeafEntry
            } else {
                PagingError::NotMapped
            });
        }
        if level > target {
            let mut tree = Self::build_split(current, level, vaddr, target, update)?;
            let root = tree.root_paddr();
            let replacement =
                PTEntry::new_table(A::make_private_address(root), A::PTFlags::parent_flags());
            let flush = MayNeedFlush::<A::TlbFlushTok>::new(vaddr, level);
            if A::requires_break_before_make(current.raw(), replacement.raw(), level) {
                let mut invalidated = InvalidatedLeaf::new(slot);
                flush_transition(flush, all_cpus);
                // SAFETY: the subtree remains private during the architecture's BBM barrier.
                unsafe {
                    Self::refresh_split(
                        tree.page_mut(),
                        invalidated.snapshot(),
                        level,
                        vaddr,
                        target,
                        update,
                    )
                };
                invalidated.publish(replacement);
                tree.release();
            } else {
                loop {
                    match slot.compare_exchange(current, replacement) {
                        Ok(_) => break,
                        Err(latest) => {
                            current = latest;
                            // SAFETY: the subtree is private until the compare-exchange publishes it.
                            unsafe {
                                Self::refresh_split(
                                    tree.page_mut(),
                                    current,
                                    level,
                                    vaddr,
                                    target,
                                    update,
                                )
                            };
                        }
                    }
                }
                tree.release();
                flush_transition(flush, all_cpus);
            }
            return Ok(MayNeedFlush::none());
        }

        match update {
            LeafUpdate::Split => Ok(MayNeedFlush::none()),
            LeafUpdate::UpdateEncryption(_) => {
                let desired = update.apply(current, level);
                let clear = current.raw() & !desired.raw();
                let set = desired.raw() & !current.raw();
                if clear == 0 && set == 0 {
                    return Ok(MayNeedFlush::none());
                }
                let flush = MayNeedFlush::<A::TlbFlushTok>::new(vaddr, level);
                if clear == 0 {
                    slot.fetch_or(set);
                    Ok(flush)
                } else if set == 0 {
                    slot.fetch_and(!clear);
                    Ok(flush)
                } else {
                    // Two disjoint tags must never appear in a malformed present intermediate.
                    let mut invalidated = InvalidatedLeaf::new(slot);
                    flush_transition(flush, all_cpus);
                    let old = invalidated.snapshot();
                    invalidated.publish(update.apply(old, level));
                    Ok(MayNeedFlush::none())
                }
            }
            LeafUpdate::Protect(_) => loop {
                let desired = update.apply(current, level);
                if desired.raw() == current.raw() {
                    return Ok(MayNeedFlush::none());
                }
                // Permission replacement must preserve A/D that raced with this snapshot.
                match slot.compare_exchange(current, desired) {
                    Ok(_) => return Ok(MayNeedFlush::new(vaddr, level)),
                    Err(entry) => {
                        current = entry;
                    }
                }
            },
        }
    }

    unsafe fn refresh_split(
        page: &mut Self,
        entry: PTEntry<A>,
        level: PageLevel,
        vaddr: VirtAddr,
        target: PageLevel,
        update: LeafUpdate<A>,
    ) {
        let child_level = level.child().unwrap();
        for idx in 0..Self::COUNT {
            let slot = page.entry_mut(idx);
            let mut child = entry.split_child(level, idx);
            if idx == entry_index(vaddr, child_level) {
                if child_level > target {
                    let table = *slot;
                    let child_page = unsafe {
                        &mut *P::paddr_to_vaddr(PhysAddr::from(table.address()))
                            .as_mut_ptr::<Self>()
                    };
                    unsafe {
                        Self::refresh_split(child_page, child, child_level, vaddr, target, update)
                    };
                    child = table;
                } else {
                    child = update.apply(child, child_level);
                }
            }
            *slot = child.for_publication();
        }
    }

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
        for idx in 0..Self::COUNT {
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
                child = child.with_leaf_flags(child_level, flags);
            }
            *page.entry_mut(idx) = child.for_publication();
            if let Some(subtree) = subtree {
                subtree.release();
            }
        }
        Ok(tree)
    }

    unsafe fn refresh_range_split(
        page: &mut Self,
        entry: PTEntry<A>,
        level: PageLevel,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) {
        let child_level = level.child().unwrap();
        for idx in 0..Self::COUNT {
            let slot = page.entry_mut(idx);
            let table = *slot;
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
                *slot = table.for_publication();
            } else {
                if first < last {
                    child = child.with_leaf_flags(child_level, flags);
                }
                *slot = child.for_publication();
            }
        }
    }

    /// Protects the valid prefix with one barrier if either boundary needs a split.
    /// Allocation failure leaves the entire original leaf being prepared unchanged;
    /// earlier original leaves may still be protected.
    ///
    /// # Safety
    /// The well-formed tree must stay pinned, and all software writers must be
    /// excluded throughout the batch and its unwind. Only hardware A/D writes
    /// may race. Flags and range alignment must already be checked. Local scope
    /// requires no stale remote translations or migration during the transition.
    pub(crate) unsafe fn mprotect_range(
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
            let (result, deferred) = Self::protect_leaf_range(&root, range_start, range_end, flags);
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
            &mut |_, entry, level, cursor, next| {
                if !entry.is_leaf(level) {
                    return Err(PagingError::NotMapped);
                }
                let base = cursor & !(level.size() - 1);
                let partial = cursor != base || next - cursor != level.size();
                if partial {
                    let boundary = if cursor == range_start {
                        0
                    } else if next == range_end {
                        1
                    } else {
                        return Err(PagingError::InvalidRange);
                    };
                    match Self::build_range_split(entry, level, cursor - base, next - base, flags) {
                        Ok(tree) => {
                            boundary_splits[boundary] =
                                Some(RangeSplit { base, level, original: entry, tree });
                        }
                        Err(error) => return Err(error),
                    }
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
                Self::protect_leaf_range(&root, range_start, prefix_end, flags);
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
                &mut |slot, entry, level, cursor, next| {
                    let base = cursor & !(level.size() - 1);
                    if let Some(index) = boundary_splits
                        .iter()
                        .position(|split| matches!(split, Some(split) if split.base == base))
                    {
                        let split = boundary_splits[index].as_mut().unwrap();
                        let replacement = PTEntry::new_table(
                            A::make_private_address(split.tree.root_paddr()),
                            A::PTFlags::parent_flags(),
                        );
                        let mut current = entry;
                        if current.raw() != split.original.raw() {
                            // SAFETY: the tree remains private until this CAS publishes its root.
                            unsafe {
                                Self::refresh_range_split(
                                    split.tree.page_mut(),
                                    current,
                                    level,
                                    cursor - base,
                                    next - base,
                                    flags,
                                )
                            };
                        }
                        loop {
                            match slot.compare_exchange(current, replacement) {
                                Ok(_) => break,
                                Err(latest) => {
                                    current = latest;
                                    // SAFETY: the tree remains private until this CAS publishes its root.
                                    unsafe {
                                        Self::refresh_range_split(
                                            split.tree.page_mut(),
                                            current,
                                            level,
                                            cursor - base,
                                            next - base,
                                            flags,
                                        )
                                    };
                                }
                            }
                        }
                        boundary_splits[index].take().unwrap().tree.release();
                    } else {
                        let mut current = entry;
                        loop {
                            let desired = current.with_leaf_flags(level, flags);
                            if desired.raw() == current.raw() {
                                break;
                            }
                            match slot.compare_exchange(current, desired) {
                                Ok(_) => break,
                                Err(latest) => current = latest,
                            }
                        }
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
            &mut |slot, entry, level, cursor, next| {
                let base = cursor & !(level.size() - 1);
                if boundary_splits
                    .iter()
                    .any(|split| matches!(split, Some(split) if split.base == base))
                {
                    slot.fetch_and(!A::PTFlags::present_bit());
                } else {
                    let mut current = entry;
                    loop {
                        let desired = current.with_leaf_flags(level, flags);
                        if desired.raw() == current.raw() {
                            break;
                        }
                        match slot.compare_exchange(current, desired) {
                            Ok(_) => break,
                            Err(latest) => current = latest,
                        }
                    }
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
            &mut |slot, entry, level, cursor, next| {
                invalidated.start = cursor;
                let base = cursor & !(level.size() - 1);
                let old = PTEntry::from_bits(entry.raw() | A::PTFlags::present_bit());
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
                    slot.store(PTEntry::new_table(
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

    /// Maps `vaddr` to `paddr` at `target`, building the tables above it. The
    /// walk that got here reports an entry already present, so what this finds
    /// is either empty or a table it has to descend.
    pub fn do_map(
        map: Mapping<'_, A>,
        vaddr: VirtAddr,
        paddr: PhysAddr,
        target: PageLevel,
        spec: MapSpec<A>,
    ) -> Result<(), PagingError> {
        assert!(vaddr.is_aligned(target.size()));
        assert!(paddr.is_aligned(target.size()));
        let map = Self::alloc_pte_down(map, vaddr, target, A::filter_flags(spec.parent_flags))?;
        if map.level != target {
            return Err(PagingError::AllocFrame);
        }
        let addr = if spec.shared {
            A::make_shared_address(paddr)
        } else {
            A::make_private_address(paddr)
        };
        let flags = A::filter_flags(spec.flags);
        let flags = if target.is_leaf() { flags } else { flags.with(A::PTFlags::HUGE) };
        map.entry.set(addr, flags);
        Ok(())
    }

    /// Clears the entry if it maps a page of exactly `target`'s size, and
    /// returns what it held.
    pub fn do_unmap_at(map: Mapping<'_, A>, target: PageLevel) -> Option<PTEntry<A>> {
        if map.level != target || !map.entry.is_leaf(map.level) {
            return None;
        }
        let entry = *map.entry;
        map.entry.clear();
        Some(entry)
    }

    /// Clears whatever leaf the walk stopped at, and reports its level.
    pub fn do_unmap(map: Mapping<'_, A>) -> Option<PageLevel> {
        if !map.entry.is_leaf(map.level) {
            return None;
        }
        map.entry.clear();
        Some(map.level)
    }

    /// Retags the page holding `vaddr` as shared, splitting larger pages so
    /// that only a page of `target`'s size is retagged.
    pub fn do_set_shared(
        map: Mapping<'_, A>,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> Result<(), PagingError> {
        if map.level < target || !map.entry.is_leaf(map.level) {
            return Err(PagingError::NotMapped);
        }
        let prepared = Self::prepare_update(
            *map.entry,
            map.level,
            vaddr,
            target,
            LeafUpdate::UpdateEncryption(true),
        )?;
        *map.entry = prepared;
        Ok(())
    }

    /// Retags the page holding `vaddr` as private, splitting as
    /// [`Self::do_set_shared`] does.
    pub fn do_set_encrypted(
        map: Mapping<'_, A>,
        vaddr: VirtAddr,
        target: PageLevel,
    ) -> Result<(), PagingError> {
        if map.level < target || !map.entry.is_leaf(map.level) {
            return Err(PagingError::NotMapped);
        }
        let prepared = Self::prepare_update(
            *map.entry,
            map.level,
            vaddr,
            target,
            LeafUpdate::UpdateEncryption(false),
        )?;
        *map.entry = prepared;
        Ok(())
    }
}

#[cfg(all(test, target_arch = "x86_64"))]
#[path = "../../../tests/unit/ptpage.rs"]
mod view_tests;
