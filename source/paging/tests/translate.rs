//! Translation-path regressions for direct-mapped allocators.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{flags, table, Allocator, Host};
use paging::address::{PhysAddr, VirtAddr};
use paging::level::Lvl;
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::PageTable;
use paging::X86Paging;

const BASE: usize = 0x4000_0000;
const FRAME: usize = 0x4_0000_0000;

/// Direct-map provider counting snapshots acquired by one translation.
struct CountingDirectMap;

static DIRECT_MAP_CALLS: AtomicUsize = AtomicUsize::new(0);

unsafe impl DirectMappedAllocator for CountingDirectMap {
    fn direct_map() -> (core::ops::Range<PhysAddr>, VirtAddr) {
        DIRECT_MAP_CALLS.fetch_add(1, Ordering::Relaxed);
        Allocator::direct_map()
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        Allocator::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: this provider delegates the allocator domain unchanged.
        unsafe { Allocator::deallocate_table_page(paddr) };
    }
}

#[cfg(feature = "concurrent")]
type CountingTable = PageTable<X86Paging<Host>, CountingDirectMap, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type CountingTable = PageTable<X86Paging<Host>, CountingDirectMap, Lvl<3>>;

#[test]
fn translation_snapshots_the_direct_map_once() {
    let (_arena, table) = table();
    #[cfg(not(feature = "concurrent"))]
    let mut table = table;
    table.map_4k(BASE.into(), FRAME.into(), flags(), false).unwrap();

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

    DIRECT_MAP_CALLS.store(0, Ordering::Relaxed);
    assert_eq!(table.phys_addr(BASE.into()), Ok(FRAME.into()));
    assert_eq!(DIRECT_MAP_CALLS.load(Ordering::Relaxed), 1);
}
