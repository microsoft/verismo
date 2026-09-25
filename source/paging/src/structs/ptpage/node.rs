//! The page-table page, the frame a walk resolves to, and the edits a single
//! entry can undergo. Entries of a live table are only ever read and written
//! atomically, one word at a time, because the MMU writes them too.
use core::marker::PhantomData;
use core::sync::atomic::AtomicUsize;

use bitflags::Flags;

use super::tree::{SplitLeafChange, SplitLeafEncryption};
use super::{PTPageTree, WalkLevelImpl};
use crate::structs::address::{Address, PhysAddr, VirtAddr, LOW_CANONICAL_END};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::sizes::{entry_index, PageSize, PT_ENTRY_COUNT};
use crate::structs::tlb::{MayNeedFlush, TlbFlush};

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta, P: PagingAllocator> {
    entries: [AtomicUsize; PT_ENTRY_COUNT],
    dummy: PhantomData<(A, P)>,
}

/// One mutable entry in an unpublished tree.
struct UnpublishedMapping<'a, A: ArchPagingMeta> {
    level: PageLevel,
    entry: &'a mut PTEntry<A>,
}

/// What a walk found: a physical address, and the size of the page it sits in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Translation<A: ArchPagingMeta> {
    paddr: PhysAddr,
    level: PageLevel,
    dummy: PhantomData<A>,
}

/// Restores one temporarily invalidated leaf unless publication disarms it.
struct InvalidatedLeaf<'tree, A: ArchPagingMeta> {
    pte_ref: PTEntryRef<'tree, A>,
    active: bool,
}

/// Refreshes staged split descendants through statically selected child levels.
pub(crate) trait SplitRefreshLevel: InnerLevel + WalkLevelImpl
where
    Self::Child: WalkLevelImpl,
{
    unsafe fn refresh_split_child<A, P, PS, C>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>;
}

impl SplitRefreshLevel for Lvl<1> {
    unsafe fn refresh_split_child<A, P, PS, C>(_: PTEntry<A>, _: PTEntry<A>, _: Page<PS>, _: C)
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
    {
        unreachable!("leaf-level split cannot descend further")
    }
}

unsafe fn refresh_split_child_at<A, P, L, PS, C>(
    table: PTEntry<A>,
    child: PTEntry<A>,
    target_page: Page<PS>,
    change: C,
) where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: SplitRefreshLevel,
    L::Child: WalkLevelImpl,
    PS: PageSize,
    C: SplitLeafChange<A>,
{
    let child_page = unsafe {
        &mut *P::paddr_to_vaddr(PhysAddr::from(table.address())).as_mut_ptr::<PTPage<A, P>>()
    };
    unsafe { child_page.refresh_split::<L, PS, C>(child, target_page, change) };
}

impl SplitRefreshLevel for Lvl<2> {
    unsafe fn refresh_split_child<A, P, PS, C>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
    {
        unsafe { refresh_split_child_at::<A, P, Lvl<1>, PS, C>(table, child, target_page, change) };
    }
}

impl SplitRefreshLevel for Lvl<3> {
    unsafe fn refresh_split_child<A, P, PS, C>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
    {
        unsafe { refresh_split_child_at::<A, P, Lvl<2>, PS, C>(table, child, target_page, change) };
    }
}

impl SplitRefreshLevel for Lvl<4> {
    unsafe fn refresh_split_child<A, P, PS, C>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        C: SplitLeafChange<A>,
    {
        unsafe { refresh_split_child_at::<A, P, Lvl<3>, PS, C>(table, child, target_page, change) };
    }
}

/// Conservative TLB coverage accumulated from the leaves changed by a range update.
#[derive(Default)]
pub(crate) struct FlushFootprint {
    range: Option<(usize, usize, PageLevel)>,
    all: bool,
}

impl<'a, A: ArchPagingMeta> UnpublishedMapping<'a, A> {
    fn new(level: PageLevel, entry: &'a mut PTEntry<A>) -> Self {
        Self { level, entry }
    }
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

impl<'tree, A: ArchPagingMeta> InvalidatedLeaf<'tree, A> {
    /// Inputs: live leaf reference.
    /// Requires: excluded software writers.
    /// Returns: rollback guard.
    fn new(pte_ref: PTEntryRef<'tree, A>) -> Self {
        pte_ref.fetch_and(!A::PTFlags::present_bit());
        Self { pte_ref, active: true }
    }
}

impl<A: ArchPagingMeta> Drop for InvalidatedLeaf<'_, A> {
    /// Inputs: rollback guard.
    /// Requires: pinned entry.
    /// Returns: nothing.
    fn drop(&mut self) {
        if self.active {
            // The old encoding stays in place, including history written during the barrier.
            self.pte_ref.fetch_or(A::PTFlags::present_bit());
        }
    }
}

impl<'tree, A: ArchPagingMeta> InvalidatedLeaf<'tree, A> {
    /// Inputs: invalidated guard.
    /// Requires: active leaf.
    /// Returns: valid-form snapshot.
    fn snapshot(&self) -> PTEntry<A> {
        self.pte_ref.load().with_present()
    }

    /// Inputs: replacement entry.
    /// Requires: active guard.
    /// Returns: nothing.
    fn publish(&mut self, entry: PTEntry<A>) {
        self.pte_ref.store(entry);
        self.active = false;
    }
}

impl FlushFootprint {
    pub(crate) fn token<T: TlbFlush>(&self) -> MayNeedFlush<T> {
        if self.all {
            MayNeedFlush::all()
        } else if let Some((start, end, level)) = self.range {
            MayNeedFlush::new_range(start.into(), end.into(), level)
        } else {
            MayNeedFlush::none()
        }
    }

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
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// A zeroed table page, and its clean physical address.
    pub fn alloc() -> Result<(*mut Self, PhysAddr), PagingError> {
        let paddr = P::allocate_zeroed_table_page()?;
        let page = P::paddr_to_vaddr(paddr).as_mut_ptr::<Self>();
        Ok((page, paddr))
    }
}

impl<A: ArchPagingMeta, P: DirectMappedAllocator> PTPage<A, P> {
    /// Inputs: private tree and mapping.
    /// Requires: exclusive unpublished pages.
    /// Returns: map status.
    pub(super) unsafe fn map_unpublished<PS: PageSize>(
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
            if entry.is_present_table(level) {
                // SAFETY: this walk only follows private, exclusively owned pages.
                page = unsafe { &mut *Self::child_of(entry).unwrap() };
                level = level.child().unwrap();
            } else if entry.present() {
                return Err(PagingError::EntryAlreadyPresent { level });
            } else {
                return Self::do_map(
                    UnpublishedMapping::new(level, entry),
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
        unsafe { &*page }.entry(index).load()
    }

    pub(crate) fn set_leaf_flags(entry: &mut PTEntry<A>, flags: A::PTFlags) {
        let mask = A::leaf_flags_mask();
        entry.clear_flags(mask);
        entry.set_flags(flags & mask);
    }

    pub(crate) fn entry(&self, index: usize) -> PTEntryRef<'_, A> {
        PTEntryRef::new(&self.entries[index])
    }

    pub(crate) fn entry_mut(&mut self, index: usize) -> &mut PTEntry<A> {
        let word = self.entries[index].get_mut();
        // SAFETY: PTEntry is transparent over usize; the exclusive page borrow
        // excludes all software and hardware access to this word.
        unsafe { &mut *core::ptr::from_mut(word).cast::<PTEntry<A>>() }
    }
}

impl<A: ArchPagingMeta, P: PagingAllocator> PTPage<A, P> {
    /// Inputs: mapping and target.
    /// Requires: private path.
    /// Returns: deepest prepared mapping.
    fn alloc_pte_down<'a, PS: PageSize>(
        map: UnpublishedMapping<'a, A>,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<UnpublishedMapping<'a, A>, PagingError> {
        let target = PS::LEVEL;
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
            map = UnpublishedMapping::new(child_level, entry);
        }
        Ok(map)
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

    /// Inputs: leaf and replacement.
    /// Requires: pinned excluded entry.
    /// Returns: pending flush.
    /// # Safety
    /// `pte_ref` must remain allocated at `level`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Local flushing requires no stale remote translations or migration.
    pub(super) unsafe fn replace_leaf_encryption<L: LevelSpec>(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
        vaddr: VirtAddr,
        shared: bool,
        all_cpus: bool,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        loop {
            let desired = SplitLeafEncryption(shared).apply(current);
            if desired.raw() == current.raw() {
                return MayNeedFlush::none();
            }
            let flush = Self::flush_for_leaf(vaddr, L::LEVEL);
            if A::requires_break_before_make::<L>(current.raw(), desired.raw()) {
                let mut invalidated = InvalidatedLeaf::new(pte_ref);
                flush_transition(flush, all_cpus);
                let latest = invalidated.snapshot();
                invalidated.publish(SplitLeafEncryption(shared).apply(latest));
                return MayNeedFlush::none();
            }
            match pte_ref.compare_exchange(current, desired) {
                Ok(_) => return flush,
                Err(latest) => current = latest,
            }
        }
    }

    /// Publishes a fully prepared private split tree.
    ///
    /// # Safety
    /// `pte_ref` must remain allocated at `L::LEVEL`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Exclusion must outlive unwinding. Local flushing also requires no stale
    /// remote translations and no migration through the entire transition.
    pub(super) unsafe fn publish_prepared_split<L, PS, C>(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
        mut tree: PTPageTree<A, P, L::Child>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
    where
        L: SplitRefreshLevel,
        L::Child: WalkLevelImpl,
        PS: PageSize,
        C: SplitLeafChange<A>,
    {
        let level = L::LEVEL;
        let vaddr = target_page.start_address();
        let root = tree.root_paddr();
        let replacement =
            PTEntry::new_table(A::make_private_address(root), A::PTFlags::parent_flags());
        let flush = MayNeedFlush::<A::TlbFlushTok>::new(vaddr, level);
        if A::requires_break_before_make::<L>(current.raw(), replacement.raw()) {
            let mut invalidated = InvalidatedLeaf::new(pte_ref);
            flush_transition(flush, all_cpus);
            // SAFETY: the subtree remains private during the architecture's BBM barrier.
            unsafe {
                tree.root_page_mut().refresh_split::<L, PS, C>(
                    invalidated.snapshot(),
                    target_page,
                    change,
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
                        tree.root_page_mut().refresh_split::<L, PS, C>(current, target_page, change)
                    };
                }
            }
        }
        tree.release();
        flush_transition(flush, all_cpus);
        Ok(MayNeedFlush::none())
    }

    /// # Safety
    /// `pte_ref` must remain allocated at `level` with software writers excluded,
    /// and `current` must be its locked leaf observation.
    #[inline(always)]
    pub(crate) unsafe fn update_leaf_flags_in_place(
        pte_ref: PTEntryRef<'_, A>,
        current: PTEntry<A>,
        level: PageLevel,
        vaddr: VirtAddr,
        flags: A::PTFlags,
    ) -> MayNeedFlush<A::TlbFlushTok> {
        let mut desired = current;
        Self::set_leaf_flags(&mut desired, flags);
        if desired.raw() == current.raw() {
            return MayNeedFlush::none();
        }

        desired = pte_ref.swap(PTEntry::empty());
        Self::set_leaf_flags(&mut desired, flags);
        pte_ref.store(desired);
        Self::flush_for_leaf(vaddr, level)
    }

    /// Inputs: private page and leaf snapshot.
    /// Requires: matching split shape.
    /// Returns: nothing.
    pub(super) unsafe fn refresh_split<L: SplitRefreshLevel, PS: PageSize, C: SplitLeafChange<A>>(
        &mut self,
        entry: PTEntry<A>,
        target_page: Page<PS>,
        change: C,
    ) where
        L::Child: WalkLevelImpl,
    {
        let level = L::LEVEL;
        let target = PS::LEVEL;
        let vaddr = target_page.start_address();
        let child_level = L::Child::LEVEL;
        let target_index = entry_index(vaddr, child_level);
        for idx in 0..PT_ENTRY_COUNT {
            let pte_ref = self.entry_mut(idx);
            let mut child = entry.split_child(level, idx);
            if idx != target_index {
                *pte_ref = child;
                continue;
            }
            if child_level > target {
                let table = *pte_ref;
                unsafe { L::refresh_split_child::<A, P, PS, C>(table, child, target_page, change) };
                child = table;
            } else {
                child = change.apply(child);
            }
            *pte_ref = child;
        }
    }

    /// Maps `page` to `frame`, building the tables above it. The
    /// walk that got here reports an entry already present, so what this finds
    /// is either empty or a table it has to descend.
    fn do_map<PS: PageSize>(
        map: UnpublishedMapping<'_, A>,
        page: Page<PS>,
        frame: PhysFrame<PS>,
        flags: A::PTFlags,
        shared: bool,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        let target = PS::LEVEL;
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

/// Inputs: flush token and scope.
/// Requires: excluded mapping transition.
/// Returns: nothing.
fn flush_transition<T: TlbFlush>(flush: MayNeedFlush<T>, all_cpus: bool) {
    if all_cpus {
        flush.flush_tlb_global_sync();
    } else {
        flush.flush_tlb_global_percpu();
    }
}
