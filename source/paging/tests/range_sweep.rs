//! Structural regression for hierarchical range protection.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{flags, table, Allocator, Host};
use paging::address::{PhysAddr, VirtAddr};
use paging::level::Lvl;
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
use paging::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use paging::pagetable::PageTable;
use paging::{PTEntryFlags, X86Paging};

const PAGE: usize = 4096;
const PAGES: usize = 512;
const BASE: usize = 0x4000_0000;
const FRAME: usize = 0x4_0000_0000;

#[derive(Clone)]
struct ResolutionCountingAllocator {
    inner: Allocator,
    resolutions: Arc<AtomicUsize>,
}

unsafe impl PagingAllocator for ResolutionCountingAllocator {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        self.resolutions.fetch_add(1, Ordering::Relaxed);
        PagingAllocator::paddr_to_vaddr(&self.inner, paddr)
    }

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        PagingAllocator::vaddr_to_paddr(&self.inner, vaddr)
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        DirectMappedAllocator::allocate_table_page(&self.inner)
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        // SAFETY: the wrapper preserves the allocator domain and ownership transfer.
        unsafe { DirectMappedAllocator::deallocate_table_page(&self.inner, paddr) };
    }
}

#[cfg(feature = "concurrent")]
type CountingTable = PageTable<X86Paging<Host>, ResolutionCountingAllocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type CountingTable = PageTable<X86Paging<Host>, ResolutionCountingAllocator, Lvl<3>>;

fn readonly() -> PTEntryFlags {
    PTEntryFlags::PRESENT | PTEntryFlags::NX
}

#[test]
fn contiguous_4k_range_resolves_each_table_per_sweep_not_per_leaf() {
    let (_arena, table) = table();
    #[cfg(not(feature = "concurrent"))]
    let mut table = table;
    for page in 0..PAGES {
        table
            .map_4k(
                VirtAddr::from(BASE + page * PAGE),
                PhysAddr::from(FRAME + page * PAGE),
                flags(),
                false,
            )
            .unwrap();
    }

    #[cfg(feature = "concurrent")]
    let (allocator, locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let (allocator, root) = table.leak();
    let resolutions = Arc::new(AtomicUsize::new(0));
    let counted =
        ResolutionCountingAllocator { inner: allocator, resolutions: resolutions.clone() };
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(counted, locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let mut table = unsafe { CountingTable::from_root(counted, root) }.unwrap();
    resolutions.store(0, Ordering::Relaxed);

    let (result, pending) = table.mprotect_range(
        VirtAddr::from(BASE),
        VirtAddr::from(BASE + PAGES * PAGE),
        readonly(),
        true,
    );

    assert_eq!(result, Ok(()));
    // SAFETY: this host-backed tree is never installed in hardware.
    unsafe { pending.ignore() };
    let resolved = resolutions.load(Ordering::Relaxed);
    assert!(resolved <= 10, "boundary probes and hierarchical sweep resolved {resolved} pages");
    assert!(!table.walk(VirtAddr::from(BASE)).read().writable());
    assert!(!table.walk(VirtAddr::from(BASE + (PAGES - 1) * PAGE)).read().writable());
}
