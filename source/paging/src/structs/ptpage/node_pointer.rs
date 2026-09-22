//! Lifetime-bound access to live page-table pages.
//!
//! Concurrent paging requires reads from a `PTPage` to coexist with writes to
//! its entries. Whole-page `&PTPage` and `&mut PTPage` borrows cannot express
//! that access pattern because the mutable borrow must be exclusive.
//! `PTPagePointer` instead uses the tree lifetime only to pin the allocation
//! and grants no aliasing rights over entry contents. Each entry is observed or
//! changed through its atomic `PTEntryRef`, with writes separately serialized
//! by the controller when required.
use core::marker::PhantomData;
use core::ops::ControlFlow;
use core::ptr::NonNull;

use super::PTPage;
use super::PTPageTree;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::{InnerLevel, LevelSpec, Lvl, PageLevel};
use crate::structs::os_contract::PagingAllocator;
use crate::structs::os_contract::PagingError;
use crate::structs::page::Page;
use crate::structs::policy::KernelPolicy;
use crate::structs::sizes::PageSize;
use crate::structs::sizes::{entry_index, Huge, Regular, PT_ENTRY_COUNT};
use crate::structs::tlb::MayNeedFlush;

fn owns_all_entries(_: usize) -> bool {
    true
}

/// A non-owning page pointer; its lifetime pins memory, not entry contents.
pub(crate) struct PTPagePointer<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> {
    page: NonNull<PTPage<A, P>>,
    marker: PhantomData<(&'tree PTPage<A, P>, L)>,
}

/// An atomic observation returned by a concurrent page-table walk.
pub struct WalkResult<A: ArchPagingMeta> {
    entry: PTEntry<A>,
    level: PageLevel,
}

pub(crate) struct WalkStop<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> {
    pub(crate) page: PTPagePointer<'tree, A, P, L>,
    pub(crate) index: usize,
    page_paddr: Option<PhysAddr>,
    observed: PTEntry<A>,
}

/// Handles one page whose level is selected by [`WalkLevelImpl::dispatch`].
pub(crate) trait PageLevelHandler<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    type Output;

    fn visit_l0(self, page: PTPagePointer<'tree, A, P, Lvl<0>>) -> Self::Output;
    fn visit_l1(self, page: PTPagePointer<'tree, A, P, Lvl<1>>) -> Self::Output;
    fn visit_l2(self, page: PTPagePointer<'tree, A, P, Lvl<2>>) -> Self::Output;
    fn visit_l3(self, page: PTPagePointer<'tree, A, P, Lvl<3>>) -> Self::Output;
    fn visit_l4(self, page: PTPagePointer<'tree, A, P, Lvl<4>>) -> Self::Output;
}

/// Controls traversal after a stable visitor handles a non-table entry.
pub(crate) enum StableVisit {
    Continue,
    Revisit,
}

/// Traverses pinned tables while existing child-table links remain installed.
///
/// Implementations may update leaves or publish new child tables. They must
/// not unlink or reclaim a table page reachable by this traversal.
pub(crate) trait StableVisitor<'tree, A: ArchPagingMeta, P: PagingAllocator>: Sized {
    type Break;

    #[inline(always)]
    fn visit_l0(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<0>>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break> {
        stable_walk_l0(self, page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_l1(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<1>>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break> {
        stable_walk_inner(self, page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_l2(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<2>>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break> {
        stable_walk_inner(self, page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_l3(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<3>>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break> {
        stable_walk_inner(self, page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_l4(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<4>>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break> {
        stable_walk_inner(self, page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_point_l0(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<0>>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
    ) -> ControlFlow<Self::Break> {
        stable_visit_point_l0(self, page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn visit_point_l1(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<1>>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
    ) -> ControlFlow<Self::Break> {
        stable_visit_point_inner(self, page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn visit_point_l2(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<2>>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
    ) -> ControlFlow<Self::Break> {
        stable_visit_point_inner(self, page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn visit_point_l3(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<3>>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
    ) -> ControlFlow<Self::Break> {
        stable_visit_point_inner(self, page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn visit_point_l4(
        &mut self,
        page: PTPagePointer<'tree, A, P, Lvl<4>>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
    ) -> ControlFlow<Self::Break> {
        stable_visit_point_inner(self, page, page_paddr, vaddr)
    }

    fn visit_l0_entry(
        &mut self,
        page: &PTPagePointer<'tree, A, P, Lvl<0>>,
        page_paddr: PhysAddr,
        index: usize,
        entry: PTEntry<A>,
        start: usize,
        end: usize,
    ) -> ControlFlow<Self::Break, StableVisit>;

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
        L::Child: WalkLevelImpl;
}

#[inline(always)]
fn stable_entry_bounds(level: PageLevel, start: usize, end: usize) -> (usize, usize) {
    let page_span = level.size() * PT_ENTRY_COUNT;
    if start & (page_span - 1) == 0 && end - start == page_span {
        (0, PT_ENTRY_COUNT - 1)
    } else {
        (entry_index(VirtAddr::from(start), level), entry_index(VirtAddr::from(end - 1), level))
    }
}

#[inline(always)]
fn stable_walk_l0<'tree, A, P, V>(
    visitor: &mut V,
    page: PTPagePointer<'tree, A, P, Lvl<0>>,
    page_paddr: Option<PhysAddr>,
    start: usize,
    end: usize,
) -> ControlFlow<V::Break>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    V: StableVisitor<'tree, A, P>,
{
    let level = PageLevel::Level0;
    let span = level.size();
    let (first, last) = stable_entry_bounds(level, start, end);
    let page_paddr = page_paddr.unwrap_or_else(|| page.paddr());
    let mut cursor = start;
    let mut entry_end = (start & !(span - 1)).saturating_add(span).min(end);
    for index in first..=last {
        loop {
            let entry = page.load(index);
            match visitor.visit_l0_entry(&page, page_paddr, index, entry, cursor, entry_end) {
                ControlFlow::Continue(StableVisit::Continue) => break,
                ControlFlow::Continue(StableVisit::Revisit) => {}
                ControlFlow::Break(value) => return ControlFlow::Break(value),
            }
        }
        cursor = entry_end;
        entry_end = entry_end.saturating_add(span).min(end);
    }
    ControlFlow::Continue(())
}

#[inline(always)]
fn stable_walk_inner<'tree, A, P, L, V>(
    visitor: &mut V,
    page: PTPagePointer<'tree, A, P, L>,
    page_paddr: Option<PhysAddr>,
    start: usize,
    end: usize,
) -> ControlFlow<V::Break>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: InnerLevel + LeafSplitLevelImpl + WalkLevelImpl,
    L::Child: WalkLevelImpl,
    V: StableVisitor<'tree, A, P>,
{
    let level = L::LEVEL;
    let span = level.size();
    let (first, last) = stable_entry_bounds(level, start, end);
    let page_paddr = page_paddr.unwrap_or_else(|| page.paddr());
    let mut cursor = start;
    let mut entry_end = (start & !(span - 1)).saturating_add(span).min(end);
    for index in first..=last {
        loop {
            let entry = page.load(index);
            if let Ok(child) = page.child_from_observed(entry) {
                L::ChildLevel::visit_stable(
                    child,
                    Some(PhysAddr::from(entry.address())),
                    cursor,
                    entry_end,
                    visitor,
                )?;
                break;
            }
            match visitor.visit_inner_entry(&page, page_paddr, index, entry, cursor, entry_end) {
                ControlFlow::Continue(StableVisit::Continue) => break,
                ControlFlow::Continue(StableVisit::Revisit) => {}
                ControlFlow::Break(value) => return ControlFlow::Break(value),
            }
        }
        cursor = entry_end;
        entry_end = entry_end.saturating_add(span).min(end);
    }
    ControlFlow::Continue(())
}

#[inline(always)]
fn stable_visit_point_l0<'tree, A, P, V>(
    visitor: &mut V,
    page: PTPagePointer<'tree, A, P, Lvl<0>>,
    page_paddr: Option<PhysAddr>,
    vaddr: VirtAddr,
) -> ControlFlow<V::Break>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    V: StableVisitor<'tree, A, P>,
{
    let level = PageLevel::Level0;
    let index = entry_index(vaddr, level);
    let page_paddr = page_paddr.unwrap_or_else(|| page.paddr());
    let start = vaddr.bits() & !(level.size() - 1);
    let end = start.saturating_add(level.size());
    loop {
        let entry = page.load(index);
        match visitor.visit_l0_entry(&page, page_paddr, index, entry, start, end) {
            ControlFlow::Continue(StableVisit::Continue) => return ControlFlow::Continue(()),
            ControlFlow::Continue(StableVisit::Revisit) => {}
            ControlFlow::Break(value) => return ControlFlow::Break(value),
        }
    }
}

#[inline(always)]
fn stable_visit_point_inner<'tree, A, P, L, V>(
    visitor: &mut V,
    page: PTPagePointer<'tree, A, P, L>,
    page_paddr: Option<PhysAddr>,
    vaddr: VirtAddr,
) -> ControlFlow<V::Break>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: InnerLevel + LeafSplitLevelImpl + WalkLevelImpl,
    L::Child: WalkLevelImpl,
    V: StableVisitor<'tree, A, P>,
{
    let level = L::LEVEL;
    let index = entry_index(vaddr, level);
    loop {
        let entry = page.load(index);
        if let Ok(child) = page.child_from_observed(entry) {
            return L::ChildLevel::visit_stable_point(
                child,
                Some(PhysAddr::from(entry.address())),
                vaddr,
                visitor,
            );
        }
        let page_paddr = page_paddr.unwrap_or_else(|| page.paddr());
        let start = vaddr.bits() & !(level.size() - 1);
        let end = start.saturating_add(level.size());
        match visitor.visit_inner_entry(&page, page_paddr, index, entry, start, end) {
            ControlFlow::Continue(StableVisit::Continue) => return ControlFlow::Continue(()),
            ControlFlow::Continue(StableVisit::Revisit) => {}
            ControlFlow::Break(value) => return ControlFlow::Break(value),
        }
    }
}

struct FreeChildrenVisitor<F> {
    owns_entry: F,
}

struct GrowUninstalledVisitor<A: ArchPagingMeta, PS: PageSize> {
    target_page: Page<PS>,
    parent_flags: A::PTFlags,
}

/// The typed page and entry where a page-table walk stopped.
pub(crate) enum WalkPosition<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    Level0(WalkStop<'tree, A, P, Lvl<0>>),
    Level1(WalkStop<'tree, A, P, Lvl<1>>),
    Level2(WalkStop<'tree, A, P, Lvl<2>>),
    Level3(WalkStop<'tree, A, P, Lvl<3>>),
    Level4(WalkStop<'tree, A, P, Lvl<4>>),
}

type WalkStep<'tree, A, P, L> = Result<
    (PTPagePointer<'tree, A, P, <L as WalkLevelImpl>::ChildLevel>, PhysAddr),
    WalkPosition<'tree, A, P>,
>;

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

impl<'tree, A: ArchPagingMeta, P: PagingAllocator> WalkPosition<'tree, A, P> {
    #[inline(always)]
    pub(crate) fn level(&self) -> PageLevel {
        match self {
            Self::Level0(_) => PageLevel::Level0,
            Self::Level1(_) => PageLevel::Level1,
            Self::Level2(_) => PageLevel::Level2,
            Self::Level3(_) => PageLevel::Level3,
            Self::Level4(_) => PageLevel::Level4,
        }
    }

    #[inline(always)]
    pub(crate) fn observed(&self) -> PTEntry<A> {
        match self {
            Self::Level0(stop) => stop.observed,
            Self::Level1(stop) => stop.observed,
            Self::Level2(stop) => stop.observed,
            Self::Level3(stop) => stop.observed,
            Self::Level4(stop) => stop.observed,
        }
    }

    #[inline(always)]
    pub(crate) fn walk(&self, vaddr: VirtAddr) -> WalkPosition<'tree, A, P> {
        match self {
            Self::Level0(stop) => stop.page.walk(vaddr),
            Self::Level1(stop) => stop.page.walk(vaddr),
            Self::Level2(stop) => stop.page.walk(vaddr),
            Self::Level3(stop) => stop.page.walk(vaddr),
            Self::Level4(stop) => stop.page.walk(vaddr),
        }
    }

    pub(crate) fn entry(&self) -> PTEntryRef<'tree, A> {
        match self {
            Self::Level0(stop) => stop.page.entry(stop.index),
            Self::Level1(stop) => stop.page.entry(stop.index),
            Self::Level2(stop) => stop.page.entry(stop.index),
            Self::Level3(stop) => stop.page.entry(stop.index),
            Self::Level4(stop) => stop.page.entry(stop.index),
        }
    }

    pub(crate) fn page_paddr(&self) -> PhysAddr {
        match self {
            Self::Level0(stop) => stop.page_paddr.unwrap_or_else(|| stop.page.paddr()),
            Self::Level1(stop) => stop.page_paddr.unwrap_or_else(|| stop.page.paddr()),
            Self::Level2(stop) => stop.page_paddr.unwrap_or_else(|| stop.page.paddr()),
            Self::Level3(stop) => stop.page_paddr.unwrap_or_else(|| stop.page.paddr()),
            Self::Level4(stop) => stop.page_paddr.unwrap_or_else(|| stop.page.paddr()),
        }
    }

    fn set_page_paddr(&mut self, page_paddr: Option<PhysAddr>) {
        match self {
            Self::Level0(stop) => stop.page_paddr = page_paddr,
            Self::Level1(stop) => stop.page_paddr = page_paddr,
            Self::Level2(stop) => stop.page_paddr = page_paddr,
            Self::Level3(stop) => stop.page_paddr = page_paddr,
            Self::Level4(stop) => stop.page_paddr = page_paddr,
        }
    }
}

/// Selects the supported split operation for one statically known leaf level.
pub(crate) trait LeafSplitLevelImpl: LevelSpec + Sized {
    /// # Safety
    /// The entry must stay pinned and exclude software writers.
    unsafe fn split_leaf_to<A: ArchPagingMeta, P: PagingAllocator, PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        let _ = (pte_ref, page, all_cpus);
        Err(PagingError::InvalidLevel)
    }

    /// # Safety
    /// The entry must stay pinned and exclude software writers.
    unsafe fn split_leaf_for_region<A: ArchPagingMeta, P: PagingAllocator>(
        pte_ref: PTEntryRef<'_, A>,
        vaddr: VirtAddr,
    ) -> Result<(), PagingError> {
        let _ = (pte_ref, vaddr);
        Err(PagingError::InvalidLevel)
    }
}

pub(crate) trait WalkLevelImpl: LevelSpec + Sized {
    type ChildLevel: WalkLevelImpl + LeafSplitLevelImpl;

    fn dispatch<'tree, A, P, V>(page: PTPagePointer<'tree, A, P, Self>, visitor: V) -> V::Output
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: PageLevelHandler<'tree, A, P>;

    fn visit_stable<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>;

    fn visit_stable_point<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>;

    fn walk<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P>;

    fn position<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        index: usize,
        page_paddr: Option<PhysAddr>,
        observed: PTEntry<A>,
    ) -> WalkPosition<'tree, A, P>;
}

/// A supported static root level for [`crate::pagetable::PageTable`].
#[allow(private_bounds)]
pub trait WalkLevel: WalkLevelImpl + LeafSplitLevelImpl {}

impl<L: WalkLevelImpl + LeafSplitLevelImpl> WalkLevel for L {}

impl LeafSplitLevelImpl for Lvl<0> {}

impl LeafSplitLevelImpl for Lvl<1> {
    unsafe fn split_leaf_to<A: ArchPagingMeta, P: PagingAllocator, PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        unsafe { PTPage::<A, P>::split_leaf_to::<Self, PS>(pte_ref, page, all_cpus) }
    }

    unsafe fn split_leaf_for_region<A: ArchPagingMeta, P: PagingAllocator>(
        pte_ref: PTEntryRef<'_, A>,
        vaddr: VirtAddr,
    ) -> Result<(), PagingError> {
        unsafe {
            PTPage::<A, P>::split_leaf_to::<Self, Regular>(
                pte_ref,
                Page::<Regular>::containing_address(vaddr),
                true,
            )
        }
        .map(|_| ())
    }
}

impl LeafSplitLevelImpl for Lvl<2> {
    unsafe fn split_leaf_to<A: ArchPagingMeta, P: PagingAllocator, PS: PageSize>(
        pte_ref: PTEntryRef<'_, A>,
        page: Page<PS>,
        all_cpus: bool,
    ) -> Result<MayNeedFlush<A::TlbFlushTok>, PagingError> {
        unsafe { PTPage::<A, P>::split_leaf_to::<Self, PS>(pte_ref, page, all_cpus) }
    }

    unsafe fn split_leaf_for_region<A: ArchPagingMeta, P: PagingAllocator>(
        pte_ref: PTEntryRef<'_, A>,
        vaddr: VirtAddr,
    ) -> Result<(), PagingError> {
        unsafe {
            PTPage::<A, P>::split_leaf_to::<Self, Huge>(
                pte_ref,
                Page::<Huge>::containing_address(vaddr),
                true,
            )
        }
        .map(|_| ())
    }
}

impl LeafSplitLevelImpl for Lvl<3> {}

impl LeafSplitLevelImpl for Lvl<4> {}

impl WalkLevelImpl for Lvl<0> {
    type ChildLevel = Lvl<0>;

    #[inline(always)]
    fn dispatch<'tree, A, P, V>(page: PTPagePointer<'tree, A, P, Self>, visitor: V) -> V::Output
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: PageLevelHandler<'tree, A, P>,
    {
        visitor.visit_l0(page)
    }

    #[inline(always)]
    fn visit_stable<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_l0(page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_stable_point<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_point_l0(page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn walk<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        page.finish_at(vaddr, page_paddr)
    }

    #[inline(always)]
    fn position<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        index: usize,
        page_paddr: Option<PhysAddr>,
        observed: PTEntry<A>,
    ) -> WalkPosition<'tree, A, P> {
        WalkPosition::Level0(WalkStop { page, index, page_paddr, observed })
    }
}

#[inline(always)]
fn walk_inner<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl>(
    page: PTPagePointer<'tree, A, P, L>,
    vaddr: VirtAddr,
    page_paddr: Option<PhysAddr>,
) -> WalkPosition<'tree, A, P>
where
{
    match page.step_at(vaddr) {
        Ok((child, child_paddr)) => L::ChildLevel::walk(child, vaddr, Some(child_paddr)),
        Err(mut result) => {
            result.set_page_paddr(page_paddr);
            result
        }
    }
}

impl WalkLevelImpl for Lvl<1> {
    type ChildLevel = Lvl<0>;

    #[inline(always)]
    fn dispatch<'tree, A, P, V>(page: PTPagePointer<'tree, A, P, Self>, visitor: V) -> V::Output
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: PageLevelHandler<'tree, A, P>,
    {
        visitor.visit_l1(page)
    }

    #[inline(always)]
    fn visit_stable<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_l1(page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_stable_point<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_point_l1(page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn walk<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        walk_inner(page, vaddr, page_paddr)
    }

    #[inline(always)]
    fn position<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        index: usize,
        page_paddr: Option<PhysAddr>,
        observed: PTEntry<A>,
    ) -> WalkPosition<'tree, A, P> {
        WalkPosition::Level1(WalkStop { page, index, page_paddr, observed })
    }
}

impl WalkLevelImpl for Lvl<2> {
    type ChildLevel = Lvl<1>;

    #[inline(always)]
    fn dispatch<'tree, A, P, V>(page: PTPagePointer<'tree, A, P, Self>, visitor: V) -> V::Output
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: PageLevelHandler<'tree, A, P>,
    {
        visitor.visit_l2(page)
    }

    #[inline(always)]
    fn visit_stable<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_l2(page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_stable_point<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_point_l2(page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn walk<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        walk_inner(page, vaddr, page_paddr)
    }

    #[inline(always)]
    fn position<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        index: usize,
        page_paddr: Option<PhysAddr>,
        observed: PTEntry<A>,
    ) -> WalkPosition<'tree, A, P> {
        WalkPosition::Level2(WalkStop { page, index, page_paddr, observed })
    }
}

impl WalkLevelImpl for Lvl<3> {
    type ChildLevel = Lvl<2>;

    #[inline(always)]
    fn dispatch<'tree, A, P, V>(page: PTPagePointer<'tree, A, P, Self>, visitor: V) -> V::Output
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: PageLevelHandler<'tree, A, P>,
    {
        visitor.visit_l3(page)
    }

    #[inline(always)]
    fn visit_stable<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_l3(page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_stable_point<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_point_l3(page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn walk<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        walk_inner(page, vaddr, page_paddr)
    }

    #[inline(always)]
    fn position<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        index: usize,
        page_paddr: Option<PhysAddr>,
        observed: PTEntry<A>,
    ) -> WalkPosition<'tree, A, P> {
        WalkPosition::Level3(WalkStop { page, index, page_paddr, observed })
    }
}

impl WalkLevelImpl for Lvl<4> {
    type ChildLevel = Lvl<3>;

    #[inline(always)]
    fn dispatch<'tree, A, P, V>(page: PTPagePointer<'tree, A, P, Self>, visitor: V) -> V::Output
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: PageLevelHandler<'tree, A, P>,
    {
        visitor.visit_l4(page)
    }

    #[inline(always)]
    fn visit_stable<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        start: usize,
        end: usize,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_l4(page, page_paddr, start, end)
    }

    #[inline(always)]
    fn visit_stable_point<'tree, A, P, V>(
        page: PTPagePointer<'tree, A, P, Self>,
        page_paddr: Option<PhysAddr>,
        vaddr: VirtAddr,
        visitor: &mut V,
    ) -> ControlFlow<V::Break>
    where
        A: ArchPagingMeta,
        P: PagingAllocator,
        V: StableVisitor<'tree, A, P>,
    {
        visitor.visit_point_l4(page, page_paddr, vaddr)
    }

    #[inline(always)]
    fn walk<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        walk_inner(page, vaddr, page_paddr)
    }

    #[inline(always)]
    fn position<'tree, A: ArchPagingMeta, P: PagingAllocator>(
        page: PTPagePointer<'tree, A, P, Self>,
        index: usize,
        page_paddr: Option<PhysAddr>,
        observed: PTEntry<A>,
    ) -> WalkPosition<'tree, A, P> {
        WalkPosition::Level4(WalkStop { page, index, page_paddr, observed })
    }
}

impl<'tree, A, P, F> PageLevelHandler<'tree, A, P> for FreeChildrenVisitor<F>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    F: Fn(usize) -> bool,
{
    type Output = ();

    fn visit_l0(self, page: PTPagePointer<'tree, A, P, Lvl<0>>) {
        for index in 0..PT_ENTRY_COUNT {
            if (self.owns_entry)(index) {
                page.swap(index, PTEntry::empty());
            }
        }
    }

    fn visit_l1(self, page: PTPagePointer<'tree, A, P, Lvl<1>>) {
        unsafe { page.free_inner(self.owns_entry) };
    }

    fn visit_l2(self, page: PTPagePointer<'tree, A, P, Lvl<2>>) {
        unsafe { page.free_inner(self.owns_entry) };
    }

    fn visit_l3(self, page: PTPagePointer<'tree, A, P, Lvl<3>>) {
        unsafe { page.free_inner(self.owns_entry) };
    }

    fn visit_l4(self, page: PTPagePointer<'tree, A, P, Lvl<4>>) {
        unsafe { page.free_inner(self.owns_entry) };
    }
}

impl<'tree, A, P, PS> PageLevelHandler<'tree, A, P> for GrowUninstalledVisitor<A, PS>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    PS: PageSize,
{
    type Output = Result<(), PagingError>;

    fn visit_l0(self, _: PTPagePointer<'tree, A, P, Lvl<0>>) -> Self::Output {
        Ok(())
    }

    fn visit_l1(self, page: PTPagePointer<'tree, A, P, Lvl<1>>) -> Self::Output {
        page.grow_inner(self.target_page, self.parent_flags)
    }

    fn visit_l2(self, page: PTPagePointer<'tree, A, P, Lvl<2>>) -> Self::Output {
        page.grow_inner(self.target_page, self.parent_flags)
    }

    fn visit_l3(self, page: PTPagePointer<'tree, A, P, Lvl<3>>) -> Self::Output {
        page.grow_inner(self.target_page, self.parent_flags)
    }

    fn visit_l4(self, page: PTPagePointer<'tree, A, P, Lvl<4>>) -> Self::Output {
        page.grow_inner(self.target_page, self.parent_flags)
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec> PTPagePointer<'tree, A, P, L> {
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
    pub(crate) fn duplicate(&self) -> Self {
        Self { page: self.page, marker: PhantomData }
    }

    #[inline(always)]
    pub(crate) fn level(&self) -> PageLevel {
        L::LEVEL
    }

    pub(crate) fn paddr(&self) -> PhysAddr {
        P::vaddr_to_paddr(VirtAddr::from(self.page.as_ptr() as usize))
    }

    #[inline(always)]
    pub(crate) fn walk(&self, vaddr: VirtAddr) -> WalkPosition<'tree, A, P>
    where
        L: WalkLevelImpl,
    {
        L::walk(self.duplicate(), vaddr, None)
    }

    #[inline(always)]
    fn finish_at(self, vaddr: VirtAddr, page_paddr: Option<PhysAddr>) -> WalkPosition<'tree, A, P>
    where
        L: WalkLevelImpl,
    {
        let level = self.level();
        let index = entry_index(vaddr, level);
        let observed = self.load(index);
        L::position(self, index, page_paddr, observed)
    }

    #[inline(always)]
    pub(crate) fn entry(&self, index: usize) -> PTEntryRef<'tree, A> {
        assert!(index < PT_ENTRY_COUNT);
        // SAFETY: construction pins the page, and the checked entry remains within it.
        unsafe { self.page.as_ref() }.entry(index)
    }

    #[inline(always)]
    pub(crate) fn load(&self, index: usize) -> PTEntry<A> {
        self.entry(index).load()
    }

    pub(crate) fn store(&self, index: usize, value: PTEntry<A>) {
        self.entry(index).store(value);
    }

    pub(crate) fn swap(&self, index: usize, value: PTEntry<A>) -> PTEntry<A> {
        self.entry(index).swap(value)
    }

    /// # Safety
    /// The page must be unpublished and exclusively accessible for the borrow.
    pub(super) unsafe fn page_mut(&mut self) -> &mut PTPage<A, P> {
        unsafe { self.page.as_mut() }
    }

    pub(super) fn entries_satisfy(&self, empty_entry: &impl Fn(PTEntry<A>) -> bool) -> bool {
        (0..PT_ENTRY_COUNT).all(|index| empty_entry(self.load(index)))
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> PTPagePointer<'tree, A, P, L> {
    #[inline(always)]
    fn step_at(self, vaddr: VirtAddr) -> WalkStep<'tree, A, P, L> {
        let level = self.level();
        let index = entry_index(vaddr, level);
        let observed = self.load(index);
        if observed.is_present_table(level) {
            let paddr = PhysAddr::from(observed.address());
            Ok((PTPagePointer::resolve(paddr), paddr))
        } else {
            Err(L::position(self, index, None, observed))
        }
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator, L: WalkLevelImpl> PTPagePointer<'tree, A, P, L> {
    /// Resolves the observed child table without reloading its parent entry.
    #[inline(always)]
    pub(crate) fn child_from_observed(
        &self,
        entry: PTEntry<A>,
    ) -> Result<PTPagePointer<'tree, A, P, L::ChildLevel>, PTEntry<A>> {
        if entry.is_present_table(self.level()) {
            Ok(PTPagePointer::resolve(PhysAddr::from(entry.address())))
        } else {
            Err(entry)
        }
    }

    /// Clears selected entries and frees their descendant tables, not data frames.
    /// # Safety
    /// Selected subtrees must be exclusively owned and quiesced, without
    /// surviving descendant references. All descendants must belong to `P`.
    pub(crate) unsafe fn free_children(&self, owns_entry: impl Fn(usize) -> bool) {
        L::dispatch(self.duplicate(), FreeChildrenVisitor { owns_entry });
    }

    unsafe fn free_inner(&self, owns_entry: impl Fn(usize) -> bool) {
        for index in 0..PT_ENTRY_COUNT {
            if !owns_entry(index) {
                continue;
            }
            let entry = self.load(index);
            let child_pa = if entry.is_present_table(L::LEVEL) {
                let child = self
                    .child_from_observed(entry)
                    .unwrap_or_else(|_| unreachable!("observed table entry must resolve"));
                let paddr = child.paddr();
                // SAFETY: selected descendants are exclusively owned and fully quiesced.
                unsafe { child.free_children(owns_all_entries as fn(usize) -> bool) };
                Some(paddr)
            } else {
                None
            };
            self.swap(index, PTEntry::empty());
            if let Some(paddr) = child_pa {
                // SAFETY: the child view has ended and the parent link is clear.
                unsafe { P::deallocate_table_page(paddr) };
            }
        }
    }

    pub(super) fn grow_uninstalled<PS: PageSize>(
        &self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        L::dispatch(self.duplicate(), GrowUninstalledVisitor { target_page, parent_flags })
    }

    fn grow_inner<PS: PageSize>(
        &self,
        target_page: Page<PS>,
        parent_flags: A::PTFlags,
    ) -> Result<(), PagingError> {
        if L::LEVEL == PS::LEVEL {
            return Ok(());
        }
        let index = entry_index(target_page.start_address(), self.level());
        let entry = self.load(index);
        match self.child_from_observed(entry) {
            Ok(child) => child.grow_uninstalled(target_page, parent_flags),
            Err(entry) if entry.present() => Err(PagingError::NotLeafEntry),
            Err(_) => {
                let child = PTPageTree::<A, P, L::ChildLevel>::new_root(KernelPolicy)?;
                child.root().grow_uninstalled(target_page, parent_flags)?;
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
