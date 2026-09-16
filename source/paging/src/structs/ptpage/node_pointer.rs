use core::ptr::NonNull;

use super::PTPage;
use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::entry::{PTEntry, PTEntryRef};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingAllocator;
use crate::structs::sizes::entry_index;

/// A non-owning page pointer; its lifetime pins memory, not entry contents.
pub(crate) struct PTPagePointer<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    page: NonNull<PTPage<A, P>>,
    allocator: &'tree P,
    mapping_offset: usize,
    fixed_mapping: bool,
    level: PageLevel,
}

/// The page and slot where a page-table walk stopped.
pub(crate) struct WalkResult<'tree, A: ArchPagingMeta, P: PagingAllocator> {
    pub(crate) page: PTPagePointer<'tree, A, P>,
    pub(crate) index: usize,
}

impl<'tree, A: ArchPagingMeta, P: PagingAllocator> WalkResult<'tree, A, P> {
    pub(crate) fn entry(&self) -> PTEntryRef<'tree, A> {
        self.page.entry(self.index)
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
    pub(crate) unsafe fn from_root(
        allocator: &'tree P,
        root_pa: PhysAddr,
        level: PageLevel,
    ) -> Self {
        Self::resolve(allocator, root_pa, level, allocator.fixed_mapping_offset())
    }

    #[inline(always)]
    fn resolve(
        allocator: &'tree P,
        paddr: PhysAddr,
        level: PageLevel,
        mapping_offset: Option<usize>,
    ) -> Self {
        let fixed_mapping = mapping_offset.is_some();
        let mapping_offset = mapping_offset.unwrap_or(0);
        let vaddr = if fixed_mapping {
            VirtAddr::from(paddr.bits().wrapping_add(mapping_offset))
        } else {
            allocator.paddr_to_vaddr(paddr)
        };
        let page = vaddr.as_mut_ptr();
        Self {
            page: NonNull::new(page).expect("null page-table view"),
            allocator,
            mapping_offset,
            fixed_mapping,
            level,
        }
    }

    #[inline(always)]
    pub(crate) fn level(&self) -> PageLevel {
        self.level
    }

    pub(crate) fn paddr(&self) -> PhysAddr {
        let vaddr = VirtAddr::from(self.page.as_ptr() as usize);
        if self.fixed_mapping {
            PhysAddr::from(vaddr.bits().wrapping_sub(self.mapping_offset))
        } else {
            self.allocator.vaddr_to_paddr(vaddr)
        }
    }

    pub(crate) fn allocator(&self) -> &P {
        self.allocator
    }

    /// Spell out the five architectural depths so optimized callers get a
    /// straight-line walk instead of a runtime level loop. This reduced the
    /// four-level benchmark median by about 4%, from 15.3 ns to 14.6 ns.
    #[inline(always)]
    pub(crate) fn walk(&self, vaddr: VirtAddr) -> WalkResult<'tree, A, P> {
        let page = Self {
            page: self.page,
            allocator: self.allocator,
            mapping_offset: self.mapping_offset,
            fixed_mapping: self.fixed_mapping,
            level: self.level,
        };

        macro_rules! descend {
            ($page:expr) => {
                match $page.step(vaddr) {
                    Ok(child) => child,
                    Err(result) => return result,
                }
            };
        }

        match page.level {
            PageLevel::Level0 => page.finish(vaddr),
            PageLevel::Level1 => descend!(page).finish(vaddr),
            PageLevel::Level2 => descend!(descend!(page)).finish(vaddr),
            PageLevel::Level3 => descend!(descend!(descend!(page))).finish(vaddr),
            PageLevel::Level4 => {
                descend!(descend!(descend!(descend!(page)))).finish(vaddr)
            }
        }
    }

    #[inline(always)]
    fn step(self, vaddr: VirtAddr) -> Result<Self, WalkResult<'tree, A, P>> {
        let index = entry_index(vaddr, self.level);
        let observed = self.load(index);
        match self.child_from_observed(observed) {
            Ok(child) => Ok(child),
            Err(_) => Err(WalkResult { page: self, index }),
        }
    }

    #[inline(always)]
    fn finish(self, vaddr: VirtAddr) -> WalkResult<'tree, A, P> {
        let index = entry_index(vaddr, self.level);
        WalkResult { page: self, index }
    }

    /// Returns the exact stopping observation, even if a table is published next.
    pub(crate) fn child(&self, index: usize) -> Result<Self, PTEntry<A>> {
        self.child_from_observed(self.load(index))
    }

    #[inline(always)]
    pub(crate) fn child_from_observed(&self, entry: PTEntry<A>) -> Result<Self, PTEntry<A>> {
        if entry.is_table(self.level) {
            Ok(Self::resolve(
                self.allocator,
                PhysAddr::from(entry.address()),
                self.level.child().unwrap(),
                self.fixed_mapping.then_some(self.mapping_offset),
            ))
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
