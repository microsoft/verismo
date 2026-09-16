//! Structural regression for hierarchical range protection.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};

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

struct ResolutionCountingAllocator;
static RESOLUTIONS: AtomicUsize = AtomicUsize::new(0);

unsafe impl PagingAllocator for ResolutionCountingAllocator {
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
        RESOLUTIONS.fetch_add(1, Ordering::Relaxed);
        Allocator::paddr_to_vaddr(paddr)
    }

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
        Allocator::vaddr_to_paddr(vaddr)
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        <Allocator as DirectMappedAllocator>::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: the wrapper preserves the allocator domain and ownership transfer.
        unsafe { <Allocator as DirectMappedAllocator>::deallocate_table_page(paddr) };
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
    let (locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let root = table.leak();
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let mut table = unsafe { CountingTable::from_root(root) }.unwrap();
    RESOLUTIONS.store(0, Ordering::Relaxed);

    let (result, pending) = table.mprotect_range(
        VirtAddr::from(BASE),
        VirtAddr::from(BASE + PAGES * PAGE),
        readonly(),
        true,
    );

    assert_eq!(result, Ok(()));
    // SAFETY: this host-backed tree is never installed in hardware.
    unsafe { pending.ignore() };
    let resolved = RESOLUTIONS.load(Ordering::Relaxed);
    assert!(resolved <= 10, "boundary probes and hierarchical sweep resolved {resolved} pages");
    assert!(!table.walk(VirtAddr::from(BASE)).read().writable());
    assert!(!table.walk(VirtAddr::from(BASE + (PAGES - 1) * PAGE)).read().writable());
}
