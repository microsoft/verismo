use core::marker::PhantomData;
use core::ptr::NonNull;

use super::PTPage;
use crate::structs::address::{PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingAllocator;
use crate::structs::sizes::entry_index;

/// A non-owning page pointer; its lifetime pins memory, not entry contents.
pub(crate) struct PTPagePointer<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    page: NonNull<PTPage<A, P>>,
    level: PageLevel,
    marker: PhantomData<&'tree PTPage<A, P>>,
}

/// The page and slot where a page-table walk stopped.
pub(crate) struct WalkResult<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    pub(crate) page: PTPagePointer<'tree, A, P>,
    pub(crate) index: usize,
    page_paddr: Option<PhysAddr>,
    #[cfg(feature = "concurrent")]
    pub(crate) observed: PTEntry<A>,
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator> WalkResult<'tree, A, P> {
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

    /// Spells out the five architectural depths so optimized callers retain a
    /// straight-line walk instead of a runtime level loop.
    #[inline(always)]
    pub(crate) fn walk(&self, vaddr: VirtAddr) -> WalkResult<'tree, A, P> {
        let page = Self { page: self.page, level: self.level, marker: PhantomData };
        let mut page_paddr = None;

        macro_rules! descend {
            ($page:expr, $level:expr, $child:expr) => {
                match $page.step_at(vaddr, $level, $child) {
                    Ok((child, child_paddr)) => {
                        page_paddr = Some(child_paddr);
                        child
                    }
                    Err(mut result) => {
                        result.page_paddr = page_paddr;
                        return result;
                    }
                }
            };
        }

        match page.level {
            PageLevel::Level0 => page.finish_at(vaddr, PageLevel::Level0, page_paddr),
            PageLevel::Level1 => descend!(page, PageLevel::Level1, PageLevel::Level0).finish_at(
                vaddr,
                PageLevel::Level0,
                page_paddr,
            ),
            PageLevel::Level2 => descend!(
                descend!(page, PageLevel::Level2, PageLevel::Level1),
                PageLevel::Level1,
                PageLevel::Level0
            )
            .finish_at(vaddr, PageLevel::Level0, page_paddr),
            PageLevel::Level3 => descend!(
                descend!(
                    descend!(page, PageLevel::Level3, PageLevel::Level2),
                    PageLevel::Level2,
                    PageLevel::Level1
                ),
                PageLevel::Level1,
                PageLevel::Level0
            )
            .finish_at(vaddr, PageLevel::Level0, page_paddr),
            PageLevel::Level4 => descend!(
                descend!(
                    descend!(
                        descend!(page, PageLevel::Level4, PageLevel::Level3),
                        PageLevel::Level3,
                        PageLevel::Level2
                    ),
                    PageLevel::Level2,
                    PageLevel::Level1
                ),
                PageLevel::Level1,
                PageLevel::Level0
            )
            .finish_at(vaddr, PageLevel::Level0, page_paddr),
        }
    }

    #[inline(always)]
    fn step_at(
        self,
        vaddr: VirtAddr,
        level: PageLevel,
        child_level: PageLevel,
    ) -> Result<(Self, PhysAddr), WalkResult<'tree, A, P>> {
        debug_assert_eq!(self.level, level);
        let index = entry_index(vaddr, level);
        let observed = self.load(index);
        if observed.is_table(level) {
            let paddr = PhysAddr::from(observed.address());
            Ok((Self::resolve(paddr, child_level), paddr))
        } else {
            #[cfg(not(feature = "concurrent"))]
            let _ = observed;
            Err(WalkResult {
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
    ) -> WalkResult<'tree, A, P> {
        debug_assert_eq!(self.level, level);
        let index = entry_index(vaddr, level);
        #[cfg(feature = "concurrent")]
        let observed = self.load(index);
        WalkResult {
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
        assert!(index < PTPage::<A, P>::COUNT);
        // SAFETY: construction pins the page, and the checked slot remains within it.
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
        (0..PTPage::<A, P>::COUNT).all(|index| empty_entry(self.load(index)))
    }
}
