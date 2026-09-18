//! Translation-path regressions for allocator address resolution.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{flags, table, Allocator, Host};
use paging::address::{PhysAddr, VirtAddr};
use paging::level::Lvl;
use paging::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use paging::pagetable::PageTable;
use paging::X86Paging;

const BASE: usize = 0x4000_0000;
const FRAME: usize = 0x4_0000_0000;

struct CountingAllocator;

static RESOLUTION_CALLS: AtomicUsize = AtomicUsize::new(0);

unsafe impl PagingAllocator for CountingAllocator {
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
        RESOLUTION_CALLS.fetch_add(1, Ordering::Relaxed);
        <Allocator as PagingAllocator>::paddr_to_vaddr(paddr)
    }

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
        <Allocator as PagingAllocator>::vaddr_to_paddr(vaddr)
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        <Allocator as DirectMappedAllocator>::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: this provider delegates the allocator domain unchanged.
        unsafe { <Allocator as DirectMappedAllocator>::deallocate_table_page(paddr) };
    }
}

#[cfg(feature = "concurrent")]
type CountingTable = PageTable<X86Paging<Host>, CountingAllocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type CountingTable = PageTable<X86Paging<Host>, CountingAllocator, Lvl<3>>;

#[test]
fn translation_uses_a_general_allocator_at_every_level() {
    let (_arena, table) = table();
    #[cfg(not(feature = "concurrent"))]
    let mut table = table;
    table
        .map(common::page_4k(BASE.into()), common::frame_4k(FRAME.into()), flags(), false)
        .unwrap();

    #[cfg(feature = "concurrent")]
    let (locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let root = table.leak();
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let table = unsafe { CountingTable::from_root(root) }.unwrap();

    RESOLUTION_CALLS.store(0, Ordering::Relaxed);
    assert_eq!(table.phys_addr(BASE.into()), Ok(FRAME.into()));
    assert_eq!(RESOLUTION_CALLS.load(Ordering::Relaxed), 4);
}
