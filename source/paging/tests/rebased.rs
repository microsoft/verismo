mod common;

use std::collections::BTreeSet;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{flags, Allocator, Arena, Host, RebasedAllocator, ARENA};
use paging::address::{PhysAddr, VirtAddr};
use paging::level::Lvl;
use paging::os_contract::DirectMappedAllocator;
use paging::pagetable::PageTable;
use paging::X86Paging;

#[cfg(not(feature = "concurrent"))]
type Table = PageTable<X86Paging<Host>, RebasedAllocator, Lvl<3>>;
#[cfg(feature = "concurrent")]
type Table = PageTable<X86Paging<Host>, RebasedAllocator, Lvl<3>, WholeTreeLock>;

fn new_table() -> Table {
    #[cfg(not(feature = "concurrent"))]
    return Table::new(flags()).unwrap();
    #[cfg(feature = "concurrent")]
    Table::new(WholeTreeLock::default(), flags()).unwrap()
}

fn assert_deallocation_panics(_arena: Arc<Arena>, page: PhysAddr) {
    assert!(catch_unwind(AssertUnwindSafe(|| unsafe {
        Allocator::deallocate_table_page(page);
    }))
    .is_err());
}

#[test]
fn allocator_rejects_invalid_and_duplicate_deallocation() {
    let arena = Arena::new(ARENA);
    let base = arena.base();
    assert_deallocation_panics(arena, PhysAddr::from(base - 4096));

    let arena = Arena::new(ARENA);
    let base = arena.base();
    assert_deallocation_panics(arena, PhysAddr::from(base + 1));

    let arena = Arena::new(ARENA);
    let allocated = Allocator::allocate_table_page().unwrap();
    assert_deallocation_panics(arena, allocated + 4096);

    let _arena = Arena::new(ARENA);
    let allocated = Allocator::allocate_table_page().unwrap();
    unsafe { Allocator::deallocate_table_page(allocated) };
    assert!(catch_unwind(AssertUnwindSafe(|| unsafe {
        Allocator::deallocate_table_page(allocated);
    }))
    .is_err());
}

#[test]
fn nonidentity_direct_map_supports_construction_translation_and_drop() {
    let arena = Arena::new(ARENA);
    let physical_base = 0x2000_1000;
    arena.rebase(physical_base);
    #[cfg_attr(feature = "concurrent", allow(unused_mut))]
    let mut table = new_table();

    assert_eq!(table.root_paddr(), PhysAddr::from(physical_base));
    for offset in [0, 4096, ARENA / 2, ARENA - 4096] {
        let vaddr = VirtAddr::from(arena.base() + offset);
        assert_eq!(table.phys_addr(vaddr), Ok(PhysAddr::from(physical_base + offset)));
        assert_eq!(table.translate(vaddr).unwrap().size(), 4096);
    }

    let vaddr = VirtAddr::from(0x4000_0000usize);
    let frame = PhysAddr::from(0x6000_0000usize);
    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.translate(vaddr).unwrap().size(), 4096);
    assert_eq!(table.validate_page_table(), Ok(()));

    drop(table);
    let freed = arena.freed();
    assert_eq!(freed.len(), arena.allocated());
    assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), freed.len());
}
