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
use core::ptr::NonNull;

use super::PTPage;
use crate::structs::address::{PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingAllocator;
use crate::structs::sizes::{entry_index, PT_ENTRY_COUNT};

/// A non-owning page pointer; its lifetime pins memory, not entry contents.
pub(crate) struct PTPagePointer<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    page: NonNull<PTPage<A, P>>,
    level: PageLevel,
    marker: PhantomData<&'tree PTPage<A, P>>,
}

/// An atomic observation returned by a concurrent page-table walk.
#[cfg(feature = "concurrent")]
pub struct WalkResult<A: ArchPagingMeta> {
    entry: PTEntry<A>,
    level: PageLevel,
}

#[cfg(feature = "concurrent")]
impl<A: ArchPagingMeta> WalkResult<A> {
    #[cfg(feature = "concurrent")]
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

/// The internal page and entry where a page-table walk stopped.
pub(crate) struct WalkPosition<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    pub(crate) page: PTPagePointer<'tree, A, P>,
    pub(crate) index: usize,
    page_paddr: Option<PhysAddr>,
    #[cfg(feature = "concurrent")]
    pub(crate) observed: PTEntry<A>,
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator> WalkPosition<'tree, A, P> {
    pub(crate) fn entry(&self) -> PTEntryRef<'tree, A> {
        self.page.entry(self.index)
    }

    #[cfg(feature = "concurrent")]
    pub(crate) fn page_paddr(&self) -> PhysAddr {
        self.page_paddr.unwrap_or_else(|| self.page.paddr())
    }
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator> PTPagePointer<'tree, A, P> {
    /// # Safety
    /// `root_pa` must identify a table at `level`. The root and all reachable
    /// table pages and links must remain well-formed, initialized, writable and
    /// pinned for the views that can reach them.
    /// Entries must be atomic-aligned; conflicting accesses must be atomic,
    /// without ordinary references into live pages. Exclusive, quiesced teardown
    /// may reclaim descendants only after ending their views and unlinking them.
    pub(crate) unsafe fn from_root(root_pa: PhysAddr, level: PageLevel) -> Self {
        Self::resolve(root_pa, level)
    }

    #[inline(always)]
    fn resolve(paddr: PhysAddr, level: PageLevel) -> Self {
        let vaddr = P::paddr_to_vaddr(paddr);
        Self::from_vaddr(vaddr, level)
    }

    #[inline(always)]
    fn from_vaddr(vaddr: VirtAddr, level: PageLevel) -> Self {
        let page = vaddr.as_mut_ptr();
        Self { page: NonNull::new(page).expect("null page-table view"), level, marker: PhantomData }
    }

    #[inline(always)]
    pub(crate) fn level(&self) -> PageLevel {
        self.level
    }

    pub(crate) fn paddr(&self) -> PhysAddr {
        P::vaddr_to_paddr(VirtAddr::from(self.page.as_ptr() as usize))
    }

    #[inline(always)]
    pub(crate) fn walk(&self, vaddr: VirtAddr) -> WalkPosition<'tree, A, P> {
        let page = Self { page: self.page, level: self.level, marker: PhantomData };
        match page.level {
            PageLevel::Level0 => Self::walk_level::<0>(page, vaddr, None),
            PageLevel::Level1 => Self::walk_level::<1>(page, vaddr, None),
            PageLevel::Level2 => Self::walk_level::<2>(page, vaddr, None),
            PageLevel::Level3 => Self::walk_level::<3>(page, vaddr, None),
            PageLevel::Level4 => Self::walk_level::<4>(page, vaddr, None),
        }
    }

    #[inline(always)]
    fn walk_child<const LEVEL: usize>(
        page: Self,
        vaddr: VirtAddr,
        page_paddr: PhysAddr,
    ) -> WalkPosition<'tree, A, P> {
        match LEVEL {
            1 => Self::walk_level::<0>(page, vaddr, Some(page_paddr)),
            2 => Self::walk_level::<1>(page, vaddr, Some(page_paddr)),
            3 => Self::walk_level::<2>(page, vaddr, Some(page_paddr)),
            4 => Self::walk_level::<3>(page, vaddr, Some(page_paddr)),
            _ => unreachable!("leaf page has no child"),
        }
    }

    #[inline(always)]
    fn walk_level<const LEVEL: usize>(
        page: Self,
        vaddr: VirtAddr,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        let level = PageLevel::at::<LEVEL>();
        if LEVEL == 0 {
            return page.finish_at(vaddr, level, page_paddr);
        }
        let child_level = level.child().unwrap();
        match page.step_at(vaddr, level, child_level) {
            Ok((child, child_paddr)) => Self::walk_child::<LEVEL>(child, vaddr, child_paddr),
            Err(mut result) => {
                result.page_paddr = page_paddr;
                result
            }
        }
    }

    #[inline(always)]
    fn step_at(
        self,
        vaddr: VirtAddr,
        level: PageLevel,
        child_level: PageLevel,
    ) -> Result<(Self, PhysAddr), WalkPosition<'tree, A, P>> {
        debug_assert_eq!(self.level, level);
        let index = entry_index(vaddr, level);
        let observed = self.load(index);
        if observed.is_table(level) {
            let paddr = PhysAddr::from(observed.address());
            Ok((Self::resolve(paddr, child_level), paddr))
        } else {
            #[cfg(not(feature = "concurrent"))]
            let _ = observed;
            Err(WalkPosition {
                page: self,
                index,
                page_paddr: None,
                #[cfg(feature = "concurrent")]
                observed,
            })
        }
    }

    #[inline(always)]
    fn finish_at(
        self,
        vaddr: VirtAddr,
        level: PageLevel,
        page_paddr: Option<PhysAddr>,
    ) -> WalkPosition<'tree, A, P> {
        debug_assert_eq!(self.level, level);
        let index = entry_index(vaddr, level);
        #[cfg(feature = "concurrent")]
        let observed = self.load(index);
        WalkPosition {
            page: self,
            index,
            page_paddr,
            #[cfg(feature = "concurrent")]
            observed,
        }
    }

    /// Returns the exact stopping observation, even if a table is published next.
    pub(crate) fn child(&self, index: usize) -> Result<Self, PTEntry<A>> {
        self.child_from_observed(self.load(index))
    }

    #[inline(always)]
    pub(crate) fn child_from_observed(&self, entry: PTEntry<A>) -> Result<Self, PTEntry<A>> {
        if entry.is_table(self.level) {
            Ok(Self::resolve(PhysAddr::from(entry.address()), self.level.child().unwrap()))
        } else {
            Err(entry)
        }
    }

    #[inline(always)]
    pub(crate) fn entry(&self, index: usize) -> PTEntryRef<'tree, A> {
        assert!(index < PT_ENTRY_COUNT);
        // SAFETY: construction pins the page, and the checked entry remains within it.
        unsafe { PTEntryRef::from_raw(PTPage::entry_ptr_mut(self.page.as_ptr(), index)) }
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

    pub(super) fn entries_satisfy(&self, empty_entry: &impl Fn(PTEntry<A>) -> bool) -> bool {
        (0..PT_ENTRY_COUNT).all(|index| empty_entry(self.load(index)))
    }
}
