//! The page-table page, the frame a walk resolves to, and the edits a single
//! entry can undergo. Entries of a live table are only ever read and written
//! atomically, one word at a time, because the MMU writes them too.
use core::marker::PhantomData;
use core::ops::ControlFlow;
use core::sync::atomic::AtomicUsize;

use bitflags::Flags;

use super::tree::StagedSplitLevel;
use super::{
    LeafSplitLevelImpl, PTPagePointer, PTPageTree, StableVisit, StableVisitor, WalkLevelImpl,
};
use crate::structs::address::{Address, PhysAddr, VirtAddr, LOW_CANONICAL_END};
use crate::structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::frame::PhysFrame;
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use crate::structs::page::Page;
use crate::structs::policy::KernelPolicy;
use crate::structs::sizes::{entry_index, PageSize, PT_ENTRY_COUNT};
use crate::structs::tlb::{MayNeedFlush, TlbFlush};

/// A page-table page: nothing but its entries.
#[repr(C, align(4096))]
pub struct PTPage<A: ArchPagingMeta, P: PagingAllocator> {
    entries: [AtomicUsize; PT_ENTRY_COUNT],
    dummy: PhantomData<(A, P)>,
}

/// One atomically observed entry in a pinned live tree.
pub(crate) struct Mapping<'tree, A: ArchPagingMeta> {
    pub(crate) pte_value: PTEntry<A>,
    pub(crate) pte_ref: PTEntryRef<'tree, A>,
    pub(crate) level: PageLevel,
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

/// An unpublished boundary split prepared for one partially covered huge leaf.
#[allow(dead_code)]
struct RangeSplit<A: ArchPagingMeta, P: PagingAllocator> {
    base: usize,
    level: PageLevel,
    original: PTEntry<A>,
    tree: RangeSplitTree<A, P>,
}

/// Owns a staged range split selected from an observed runtime leaf level.
#[allow(dead_code)]
enum RangeSplitTree<A: ArchPagingMeta, P: PagingAllocator> {
    Level0(PTPageTree<A, P, Lvl<0>>),
    Level1(PTPageTree<A, P, Lvl<1>>),
    Level2(PTPageTree<A, P, Lvl<2>>),
    Level3(PTPageTree<A, P, Lvl<3>>),
}

/// Refreshes staged split descendants through statically selected child levels.
pub(crate) trait SplitRefreshLevel: InnerLevel + WalkLevelImpl
where
    Self::Child: WalkLevelImpl,
{
    unsafe fn refresh_split_child<A, P, PS, F>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy;

    unsafe fn refresh_range_child<A, P>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator;
}

impl SplitRefreshLevel for Lvl<1> {
    unsafe fn refresh_split_child<A, P, PS, F>(_: PTEntry<A>, _: PTEntry<A>, _: Page<PS>, _: F)
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        unreachable!("leaf-level split cannot descend further")
    }

    unsafe fn refresh_range_child<A, P>(
        _: PTEntry<A>,
        _: PTEntry<A>,
        _: usize,
        _: usize,
        _: A::PTFlags,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
    {
        unreachable!("leaf-level range split cannot descend further")
    }
}

unsafe fn refresh_split_child_at<A, P, L, PS, F>(
    table: PTEntry<A>,
    child: PTEntry<A>,
    target_page: Page<PS>,
    update: F,
) where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: SplitRefreshLevel,
    L::Child: WalkLevelImpl,
    PS: PageSize,
    F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
{
    let child_page = unsafe {
        &mut *P::paddr_to_vaddr(PhysAddr::from(table.address())).as_mut_ptr::<PTPage<A, P>>()
    };
    unsafe { child_page.refresh_split::<L, PS, F>(child, target_page, update) };
}

unsafe fn refresh_range_child_at<A, P, L>(
    table: PTEntry<A>,
    child: PTEntry<A>,
    from: usize,
    to: usize,
    flags: A::PTFlags,
) where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: SplitRefreshLevel,
    L::Child: WalkLevelImpl,
{
    let child_page = unsafe {
        &mut *P::paddr_to_vaddr(PhysAddr::from(table.address())).as_mut_ptr::<PTPage<A, P>>()
    };
    unsafe { child_page.refresh_range_split::<L>(child, from, to, flags) };
}

impl SplitRefreshLevel for Lvl<2> {
    unsafe fn refresh_split_child<A, P, PS, F>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        unsafe { refresh_split_child_at::<A, P, Lvl<1>, PS, F>(table, child, target_page, update) };
    }

    unsafe fn refresh_range_child<A, P>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
    {
        unsafe { refresh_range_child_at::<A, P, Lvl<1>>(table, child, from, to, flags) };
    }
}

impl SplitRefreshLevel for Lvl<3> {
    unsafe fn refresh_split_child<A, P, PS, F>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        unsafe { refresh_split_child_at::<A, P, Lvl<2>, PS, F>(table, child, target_page, update) };
    }

    unsafe fn refresh_range_child<A, P>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
    {
        unsafe { refresh_range_child_at::<A, P, Lvl<2>>(table, child, from, to, flags) };
    }
}

impl SplitRefreshLevel for Lvl<4> {
    unsafe fn refresh_split_child<A, P, PS, F>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
        PS: PageSize,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        unsafe { refresh_split_child_at::<A, P, Lvl<3>, PS, F>(table, child, target_page, update) };
    }

    unsafe fn refresh_range_child<A, P>(
        table: PTEntry<A>,
        child: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) where
        A: ArchPagingMeta,
        P: PagingAllocator,
    {
        unsafe { refresh_range_child_at::<A, P, Lvl<3>>(table, child, from, to, flags) };
    }
}

/// Iterates the low and high canonical segments without entering the address hole.
struct CanonicalRangeCursor {
    cursor: usize,
    end: usize,
}

/// Restores PTEs that remain invalidated if a split-range publication is interrupted.
#[allow(dead_code)]
struct InvalidatedPteRollbackGuard<
    'view,
    'tree,
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevelImpl,
> {
    root: &'view PTPagePointer<'tree, A, P, L>,
    start: usize,
    end: usize,
}

struct SweepPageVisitor<'a, V> {
    visit: &'a mut V,
}

/// Conservative TLB coverage accumulated from the leaves changed by a range update.
#[derive(Default)]
pub(crate) struct FlushFootprint {
    range: Option<(usize, usize, PageLevel)>,
    all: bool,
}

const HIGH_CANONICAL_START: usize = VirtAddr::new(LOW_CANONICAL_END).as_usize();

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

impl<'tree, A, P, E, V> StableVisitor<'tree, A, P> for SweepPageVisitor<'_, V>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    V: FnMut(PhysAddr, Mapping<'tree, A>, usize, usize) -> Result<(), E>,
{
    type Break = (usize, E);

    fn visit_l0_entry(
        &mut self,
        page: &PTPagePointer<'tree, A, P, Lvl<0>>,
        page_paddr: PhysAddr,
        index: usize,
        entry: PTEntry<A>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break, StableVisit> {
        sweep_visit_entry(self, page, page_paddr, index, entry, start, end)
    }

    fn visit_inner_entry<L: InnerLevel + LeafSplitLevelImpl + WalkLevelImpl>(
        &mut self,
        page: &PTPagePointer<'tree, A, P, L>,
        page_paddr: PhysAddr,
        index: usize,
        entry: PTEntry<A>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break, StableVisit>
    where
        L::Child: WalkLevelImpl,
    {
        sweep_visit_entry(self, page, page_paddr, index, entry, start, end)
    }
}

fn sweep_visit_entry<'tree, A, P, E, V, L>(
    visitor: &mut SweepPageVisitor<'_, V>,
    page: &PTPagePointer<'tree, A, P, L>,
    page_paddr: PhysAddr,
    index: usize,
    entry: PTEntry<A>,
    start: usize,
    end: usize,
) -> ControlFlow<(usize, E), StableVisit>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    V: FnMut(PhysAddr, Mapping<'tree, A>, usize, usize) -> Result<(), E>,
{
    let mapping = Mapping { pte_value: entry, pte_ref: page.entry(index), level: L::LEVEL };
    match (visitor.visit)(page_paddr, mapping, start, end) {
        Ok(()) => ControlFlow::Continue(StableVisit::Continue),
        Err(error) => ControlFlow::Break((start, error)),
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

impl CanonicalRangeCursor {
    /// Inputs: canonical bounds.
    /// Requires: ordered range.
    /// Returns: initialized cursor.
    fn new(start: usize, end: usize) -> Self {
        let cursor = if start == LOW_CANONICAL_END { HIGH_CANONICAL_START } else { start };
        Self { cursor, end }
    }

    /// Inputs: cursor state.
    /// Requires: none.
    /// Returns: current canonical position.
    fn position(&self) -> usize {
        self.cursor
    }
}

impl Iterator for CanonicalRangeCursor {
    type Item = (usize, usize);

    /// Inputs: cursor state.
    /// Requires: canonical bounds.
    /// Returns: next valid segment.
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

impl<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> Drop
    for InvalidatedPteRollbackGuard<'_, '_, A, P, L>
{
    /// Inputs: rollback guard.
    /// Requires: pinned excluded range.
    /// Returns: nothing.
    fn drop(&mut self) {
        let _ = PTPage::<A, P>::sweep_range(
            self.root,
            VirtAddr::from(self.start),
            VirtAddr::from(self.end),
            &mut |_, mapping, _, _| {
                if !mapping.pte_value.present() {
                    mapping.pte_ref.fetch_or(A::PTFlags::present_bit());
                }
                Ok::<(), core::convert::Infallible>(())
            },
        );
    }
}

#[allow(dead_code)]
impl<A: ArchPagingMeta, P: PagingAllocator> RangeSplitTree<A, P> {
    fn new(
        entry: PTEntry<A>,
        level: PageLevel,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) -> Result<Self, PagingError> {
        match level {
            PageLevel::Level0 => Err(PagingError::InvalidLevel),
            PageLevel::Level1 => {
                PTPageTree::<A, P, Lvl<1>>::new_range_split(entry, from, to, flags, KernelPolicy)
                    .map(Self::Level0)
            }
            PageLevel::Level2 => {
                PTPageTree::<A, P, Lvl<2>>::new_range_split(entry, from, to, flags, KernelPolicy)
                    .map(Self::Level1)
            }
            PageLevel::Level3 => {
                PTPageTree::<A, P, Lvl<3>>::new_range_split(entry, from, to, flags, KernelPolicy)
                    .map(Self::Level2)
            }
            PageLevel::Level4 => {
                PTPageTree::<A, P, Lvl<4>>::new_range_split(entry, from, to, flags, KernelPolicy)
                    .map(Self::Level3)
            }
        }
    }

    fn root_paddr(&self) -> PhysAddr {
        match self {
            Self::Level0(tree) => tree.root_paddr(),
            Self::Level1(tree) => tree.root_paddr(),
            Self::Level2(tree) => tree.root_paddr(),
            Self::Level3(tree) => tree.root_paddr(),
        }
    }

    /// # Safety
    /// The tree must remain unpublished and match the source leaf level.
    unsafe fn refresh(&mut self, entry: PTEntry<A>, from: usize, to: usize, flags: A::PTFlags) {
        match self {
            Self::Level0(tree) => {
                let mut root = tree.root();
                unsafe { root.page_mut().refresh_range_split::<Lvl<1>>(entry, from, to, flags) };
            }
            Self::Level1(tree) => {
                let mut root = tree.root();
                unsafe { root.page_mut().refresh_range_split::<Lvl<2>>(entry, from, to, flags) };
            }
            Self::Level2(tree) => {
                let mut root = tree.root();
                unsafe { root.page_mut().refresh_range_split::<Lvl<3>>(entry, from, to, flags) };
            }
            Self::Level3(tree) => {
                let mut root = tree.root();
                unsafe { root.page_mut().refresh_range_split::<Lvl<4>>(entry, from, to, flags) };
            }
        }
    }

    fn release(self) {
        match self {
            Self::Level0(tree) => {
                tree.release();
            }
            Self::Level1(tree) => {
                tree.release();
            }
            Self::Level2(tree) => {
                tree.release();
            }
            Self::Level3(tree) => {
                tree.release();
            }
        }
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
    pub(crate) fn sweep_range<'tree, E, L: WalkLevelImpl>(
        root: &PTPagePointer<'tree, A, P, L>,
        start: VirtAddr,
        end: VirtAddr,
        visit: &mut impl FnMut(PhysAddr, Mapping<'tree, A>, usize, usize) -> Result<(), E>,
    ) -> Result<VirtAddr, (VirtAddr, E)> {
        let mut range = CanonicalRangeCursor::new(start.bits(), end.bits());
        let mut visitor = SweepPageVisitor { visit };
        for (cursor, segment_end) in &mut range {
            let result = L::visit_stable(root.duplicate(), None, cursor, segment_end, &mut visitor);
            if let ControlFlow::Break((cursor, error)) = result {
                return Err((VirtAddr::from(cursor), error));
            }
        }
        Ok(VirtAddr::from(range.position()))
    }

    #[allow(dead_code)]
    /// Inputs: root and bounds.
    /// Requires: nonempty valid range.
    /// Returns: split requirement.
    fn range_needs_split<L: WalkLevelImpl>(
        root: &PTPagePointer<'_, A, P, L>,
        start: usize,
        end: usize,
    ) -> bool {
        let first = root.walk(VirtAddr::from(start));
        let first_level = first.level();
        let first_entry = first.entry().load();
        if first_entry.is_present_leaf(first_level) && start & (first_level.size() - 1) != 0 {
            return true;
        }

        let (last, segment_end) = if start < LOW_CANONICAL_END && end == HIGH_CANONICAL_START {
            (LOW_CANONICAL_END - 1, LOW_CANONICAL_END)
        } else {
            (end - 1, end)
        };
        let last = root.walk(VirtAddr::from(last));
        let last_level = last.level();
        let last_entry = last.entry().load();
        let last_base = segment_end.saturating_sub(1) & !(last_level.size() - 1);
        last_entry.is_present_leaf(last_level)
            && last_base.saturating_add(last_level.size()) != segment_end
    }

    #[allow(dead_code)]
    /// Inputs: root, range, and flags.
    /// Requires: excluded writers.
    /// Returns: status and footprint.
    fn update_leaf_flags_in_range<L: WalkLevelImpl>(
        root: &PTPagePointer<'_, A, P, L>,
        start: usize,
        end: usize,
        flags: A::PTFlags,
    ) -> (Result<(), PagingError>, FlushFootprint) {
        let mut footprint = FlushFootprint::default();
        let result = Self::sweep_range(
            root,
            VirtAddr::from(start),
            VirtAddr::from(end),
            &mut |_, mapping, cursor, _| {
                if !mapping.pte_value.is_present_leaf(mapping.level) {
                    return Err(PagingError::NotMapped);
                }
                let mut current = mapping.pte_value;
                loop {
                    let mut desired = current;
                    Self::set_leaf_flags(&mut desired, flags);
                    if desired.raw() == current.raw() {
                        break;
                    }
                    match mapping.pte_ref.compare_exchange(current, desired) {
                        Ok(_) => {
                            footprint.include(VirtAddr::from(cursor), mapping.level);
                            break;
                        }
                        Err(latest) => current = latest,
                    }
                }
                Ok(())
            },
        )
        .map(|_| ())
        .map_err(|(_, error)| error);
        (result, footprint)
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

    /// Inputs: entry and levels.
    /// Requires: pinned entry.
    /// Returns: validated leaf snapshot.
    fn leaf_for_update(
        pte_ref: PTEntryRef<'_, A>,
        level: PageLevel,
        target: PageLevel,
    ) -> Result<PTEntry<A>, PagingError> {
        if level < target {
            return Err(PagingError::NotLeafEntry);
        }
        let current = pte_ref.load();
        if current.is_present_leaf(level) {
            Ok(current)
        } else if current.is_present_table(level) {
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

    /// Inputs: leaf and replacement.
    /// Requires: pinned excluded entry.
    /// Returns: pending flush.
    /// # Safety
    /// `pte_ref` must remain allocated at `level`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Local flushing requires no stale remote translations or migration.
    unsafe fn replace_leaf_mapping<L: LevelSpec, F>(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
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
            let flush = Self::flush_for_leaf(vaddr, L::LEVEL);
            if A::requires_break_before_make::<L>(current.raw(), desired.raw()) {
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

    /// Publishes a fully prepared private split tree.
    ///
    /// # Safety
    /// `pte_ref` must remain allocated at `L::LEVEL`, with software writers excluded.
    /// Concurrent entry access may only atomically update hardware history bits.
    /// Exclusion must outlive unwinding. Local flushing also requires no stale
    /// remote translations and no migration through the entire transition.
    unsafe fn publish_prepared_split<L: InnerLevel, F>(
        pte_ref: PTEntryRef<'_, A>,
        mut current: PTEntry<A>,
        vaddr: VirtAddr,
        tree: PTPageTree<A, P, L::Child>,
        refresh: F,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
    where
        L::Child: WalkLevelImpl,
        F: Fn(&mut PTPage<A, P>, PTEntry<A>),
    {
        let level = L::LEVEL;
        let root = tree.root_paddr();
        let replacement =
            PTEntry::new_table(A::make_private_address(root), A::PTFlags::parent_flags());
        let flush = MayNeedFlush::<A::TlbFlushTok>::new(vaddr, level);
        if A::requires_break_before_make::<L>(current.raw(), replacement.raw()) {
            let mut invalidated = InvalidatedLeaf::new(pte_ref);
            flush_transition(flush, all_cpus);
            let mut root = tree.root();
            // SAFETY: the subtree remains private during the architecture's BBM barrier.
            refresh(unsafe { root.page_mut() }, invalidated.snapshot());
            invalidated.publish(replacement);
            tree.release();
            return Ok(MayNeedFlush::none());
        }
        loop {
            match pte_ref.compare_exchange(current, replacement) {
                Ok(_) => break,
                Err(latest) => {
                    current = latest;
                    let mut root = tree.root();
                    // SAFETY: the subtree is private until the compare-exchange publishes it.
                    refresh(unsafe { root.page_mut() }, current);
                }
            }
        }
        tree.release();
        flush_transition(flush, all_cpus);
        Ok(MayNeedFlush::none())
    }

    /// Builds and publishes a split whose target child receives `update`.
    ///
    /// # Safety
    /// `pte_ref` must stay pinned at `L::LEVEL` and software writers must remain excluded.
    unsafe fn publish_split<L: StagedSplitLevel + SplitRefreshLevel, PS: PageSize, F>(
        pte_ref: PTEntryRef<'_, A>,
        target_page: Page<PS>,
        current: PTEntry<A>,
        update: F,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
    where
        L::Child: WalkLevelImpl,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
    {
        let tree = PTPageTree::<A, P, L>::new_split(current, target_page, update, KernelPolicy)?;
        unsafe {
            Self::publish_prepared_split::<L, _>(
                pte_ref,
                current,
                target_page.start_address(),
                tree,
                |page, latest| {
                    // SAFETY: publication retains exclusive ownership of the staged tree.
                    page.refresh_split::<L, PS, F>(latest, target_page, update)
                },
                all_cpus,
            )
        }
    }

    /// Splits one leaf into its immediate typed child level.
    ///
    /// # Safety
    /// `pte_ref` must stay pinned at `L::LEVEL` and software writers must remain excluded.
    pub(crate) unsafe fn split_leaf<L: InnerLevel + WalkLevelImpl>(
        pte_ref: PTEntryRef<'_, A>,
        vaddr: VirtAddr,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
    where
        L::Child: WalkLevelImpl,
    {
        let current = Self::leaf_for_update(pte_ref, L::LEVEL, L::Child::LEVEL)?;
        let tree = PTPageTree::<A, P, L>::new_leaf_split(current, KernelPolicy)?;
        unsafe {
            Self::publish_prepared_split::<L, _>(
                pte_ref,
                current,
                vaddr,
                tree,
                |page, latest| {
                    // SAFETY: publication retains exclusive ownership of the staged tree.
                    page.refresh_leaf_split::<L>(latest)
                },
                all_cpus,
            )
        }
    }

    /// Splits a leaf directly down to `PS`.
    ///
    /// # Safety
    /// `pte_ref` must stay pinned at `L::LEVEL` and software writers must remain excluded.
    pub(crate) unsafe fn split_leaf_to<L: StagedSplitLevel + SplitRefreshLevel, PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError>
    where
        L::Child: WalkLevelImpl,
    {
        if L::Child::LEVEL == PS::LEVEL {
            return unsafe { Self::split_leaf::<L>(pte_ref, page.start_address(), all_cpus) };
        }
        let current = Self::leaf_for_update(pte_ref, L::LEVEL, PS::LEVEL)?;
        if L::LEVEL == PS::LEVEL {
            return Ok(MayNeedFlush::none());
        }
        unsafe {
            Self::publish_split::<L, PS, _>(pte_ref, page, current, |entry, _| entry, all_cpus)
        }
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
        let target = PS::LEVEL;
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
            return match level {
                PageLevel::Level1 => unsafe {
                    Self::publish_split::<Lvl<1>, PS, _>(pte_ref, page, current, update, all_cpus)
                },
                PageLevel::Level2 => unsafe {
                    Self::publish_split::<Lvl<2>, PS, _>(pte_ref, page, current, update, all_cpus)
                },
                _ => Err(PagingError::InvalidLevel),
            };
        }

        Ok(unsafe {
            Self::replace_leaf_mapping::<PS, _>(
                pte_ref,
                current,
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
        let target = PS::LEVEL;
        let vaddr = page.start_address();
        let current = Self::leaf_for_update(pte_ref, level, target)?;
        let flags = A::filter_flags(flags);
        if level > target {
            let update = |mut entry, _level| {
                Self::set_leaf_flags(&mut entry, flags);
                entry
            };
            return match level {
                PageLevel::Level1 => unsafe {
                    Self::publish_split::<Lvl<1>, PS, _>(pte_ref, page, current, update, all_cpus)
                },
                PageLevel::Level2 => unsafe {
                    Self::publish_split::<Lvl<2>, PS, _>(pte_ref, page, current, update, all_cpus)
                },
                _ => Err(PagingError::InvalidLevel),
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

    /// Inputs: private page and leaf snapshot.
    /// Requires: matching split shape.
    /// Returns: nothing.
    unsafe fn refresh_split<L: SplitRefreshLevel, PS: PageSize, F>(
        &mut self,
        entry: PTEntry<A>,
        target_page: Page<PS>,
        update: F,
    ) where
        L::Child: WalkLevelImpl,
        F: Fn(PTEntry<A>, PageLevel) -> PTEntry<A> + Copy,
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
                unsafe { L::refresh_split_child::<A, P, PS, F>(table, child, target_page, update) };
                child = table;
            } else {
                child = update(child, child_level);
            }
            *pte_ref = child;
        }
    }

    /// Rebuilds one private child table from the latest parent leaf.
    ///
    /// # Safety
    /// `self` must be the unpublished child table of `entry`.
    pub(super) unsafe fn refresh_leaf_split<L: InnerLevel>(&mut self, entry: PTEntry<A>) {
        let first = entry.split_child(L::LEVEL, 0);
        let stride = L::Child::LEVEL.size();
        for idx in 0..PT_ENTRY_COUNT {
            *self.entry_mut(idx) = PTEntry::from_bits(first.raw() + idx * stride);
        }
    }

    #[allow(dead_code)]
    /// Inputs: private page and leaf snapshot.
    /// Requires: matching range split.
    /// Returns: nothing.
    unsafe fn refresh_range_split<L: SplitRefreshLevel>(
        &mut self,
        entry: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) where
        L::Child: WalkLevelImpl,
    {
        let child_level = L::Child::LEVEL;
        for idx in 0..PT_ENTRY_COUNT {
            let pte_ref = self.entry_mut(idx);
            let table = *pte_ref;
            let mut child = entry.split_child(L::LEVEL, idx);
            let offset = idx * child_level.size();
            let first = from.saturating_sub(offset).min(child_level.size());
            let last = to.saturating_sub(offset).min(child_level.size());
            if table.is_present_table(child_level) {
                unsafe { L::refresh_range_child::<A, P>(table, child, first, last, flags) };
                *pte_ref = table;
                continue;
            }
            if first < last {
                Self::set_leaf_flags(&mut child, flags);
            }
            *pte_ref = child;
        }
    }

    #[allow(dead_code)]
    /// Inputs: entry, snapshot, and flags.
    /// Requires: pinned leaf.
    /// Returns: nothing.
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

    #[allow(dead_code)]
    /// Inputs: entry and split state.
    /// Requires: pinned excluded entry.
    /// Returns: nothing.
    unsafe fn publish_range_split_with_cas(
        pte_ref: PTEntryRef<'_, A>,
        split: &mut RangeSplit<A, P>,
        mut current: PTEntry<A>,
        from: usize,
        to: usize,
        flags: A::PTFlags,
    ) {
        let replacement = PTEntry::new_table(
            A::make_private_address(split.tree.root_paddr()),
            A::PTFlags::parent_flags(),
        );
        if current.raw() != split.original.raw() {
            unsafe { split.tree.refresh(current, from, to, flags) };
        }
        loop {
            match pte_ref.compare_exchange(current, replacement) {
                Ok(_) => return,
                Err(latest) => {
                    current = latest;
                    unsafe { split.tree.refresh(current, from, to, flags) };
                }
            }
        }
    }

    #[allow(dead_code)]
    /// Inputs: segment and range bounds.
    /// Requires: boundary segment.
    /// Returns: boundary index.
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
    #[allow(dead_code)]
    pub(crate) unsafe fn update_leaf_flags_range<L: WalkLevelImpl>(
        root: PTPagePointer<'_, A, P, L>,
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
            VirtAddr::from(range_start),
            VirtAddr::from(range_end),
            &mut |_, mapping, cursor, next| {
                let entry = mapping.pte_value;
                let level = mapping.level;
                if !entry.is_present_leaf(level) {
                    return Err(PagingError::NotMapped);
                }
                let base = cursor & !(level.size() - 1);
                let partial = cursor != base || next - cursor != level.size();
                if partial {
                    let boundary =
                        Self::range_boundary_index(cursor, next, range_start, range_end)?;
                    let tree = RangeSplitTree::<A, P>::new(
                        entry,
                        level,
                        cursor - base,
                        next - base,
                        flags,
                    )?;
                    boundary_splits[boundary] =
                        Some(RangeSplit { base, level, original: entry, tree });
                }
                footprint.include(VirtAddr::from(cursor), level);
                Ok(())
            },
        );
        let prefix_end = match planning_result {
            Ok(prefix_end) => prefix_end.bits(),
            Err((prefix_end, error)) => {
                result = Err(error);
                prefix_end.bits()
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
            match split.level {
                PageLevel::Level0 => {
                    A::requires_break_before_make::<Lvl<0>>(split.original.raw(), replacement.raw())
                }
                PageLevel::Level1 => {
                    A::requires_break_before_make::<Lvl<1>>(split.original.raw(), replacement.raw())
                }
                PageLevel::Level2 => {
                    A::requires_break_before_make::<Lvl<2>>(split.original.raw(), replacement.raw())
                }
                PageLevel::Level3 => {
                    A::requires_break_before_make::<Lvl<3>>(split.original.raw(), replacement.raw())
                }
                PageLevel::Level4 => {
                    A::requires_break_before_make::<Lvl<4>>(split.original.raw(), replacement.raw())
                }
            }
        });

        if !requires_bbm {
            let publication = Self::sweep_range(
                &root,
                VirtAddr::from(range_start),
                VirtAddr::from(prefix_end),
                &mut |_, mapping, cursor, next| {
                    let Mapping { pte_value: entry, pte_ref, level } = mapping;
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
        let mut invalidated = InvalidatedPteRollbackGuard::<A, P, L> {
            root: &root,
            start: range_start,
            end: range_start,
        };
        let invalidation = Self::sweep_range(
            &root,
            VirtAddr::from(range_start),
            VirtAddr::from(prefix_end),
            &mut |_, mapping, cursor, next| {
                let Mapping { pte_value: entry, pte_ref, level } = mapping;
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
            VirtAddr::from(invalidated.start),
            VirtAddr::from(prefix_end),
            &mut |_, mapping, cursor, next| {
                let Mapping { pte_value: entry, pte_ref, level } = mapping;
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
                    unsafe { plan.tree.refresh(old, cursor - base, next - base, flags) };
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
