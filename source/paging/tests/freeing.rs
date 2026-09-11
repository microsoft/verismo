//! Giving table pages back: the path sweep, the range sweep, and teardown.

mod common;

use common::*;
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::PageLevel;
use paging::os_contract::PagingError;

/// Unmaps `vaddr` and discharges the flush, which the freeing needs.
fn unmap(table: &mut Table, vaddr: VirtAddr) {
    let (level, flush) = table.unmap(vaddr);
    assert_eq!(level, Some(PageLevel::Level0));
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
}

#[test]
fn freeing_an_address_nothing_mapped_frees_nothing() {
    let (arena, mut table) = table();
    let vaddr = VirtAddr::from(0x80_0000_0000usize);
    // SAFETY: nothing was ever mapped there, so no walk can be in progress.
    assert_eq!(unsafe { table.free_page_table_by_addr(vaddr) }, 0);
    assert!(arena.freed().is_empty());
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn a_table_a_sibling_still_needs_is_kept() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let first = VirtAddr::from(0x4000_0000usize);
    let second = first + 4096usize;

    assert_eq!(table.map_4k(first, frame, flags(), false), Ok(()));
    assert_eq!(table.map_4k(second, frame, flags(), false), Ok(()));
    unmap(&mut table, first);

    // SAFETY: `first` is unmapped and its flush discharged.
    assert_eq!(unsafe { table.free_page_table_by_addr(first) }, 0);
    assert!(arena.freed().is_empty());
    assert_eq!(table.phys_addr(second), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn the_last_mapping_takes_its_tables_with_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    let before = arena.allocated();
    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    let built = arena.allocated() - before;
    assert_eq!(built, 3, "a four-level tree needs three tables below the root");

    unmap(&mut table, vaddr);
    // SAFETY: `vaddr` is unmapped and its flush discharged.
    assert_eq!(unsafe { table.free_page_table_by_addr(vaddr) }, built);
    assert_eq!(arena.freed().len(), built);

    // What is left still describes itself, and still works.
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn freeing_a_path_leaves_the_arena_alone() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);
    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    unmap(&mut table, vaddr);

    // SAFETY: `vaddr` is unmapped and its flush discharged.
    unsafe { table.free_page_table_by_addr(vaddr) };
    for offset in [0, ARENA / 2, ARENA - 4096] {
        let addr = arena.base() + offset;
        assert_eq!(table.phys_addr(VirtAddr::from(addr)), Ok(PhysAddr::from(addr)));
    }
    std::mem::forget(table);
}

#[test]
fn the_root_is_never_freed() {
    let (arena, mut table) = table();
    let root = table.root_paddr();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);
    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    unmap(&mut table, vaddr);

    // SAFETY: `vaddr` is unmapped and its flush discharged.
    unsafe { table.free_page_table_by_addr(vaddr) };
    assert!(!arena.freed().contains(&root.bits()));
    assert_eq!(table.root_paddr(), root);
    std::mem::forget(table);
}

#[test]
fn a_range_gives_back_the_tables_that_held_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + (2 * 1024 * 1024usize);

    assert_eq!(table.map_region_4k(start, end, frame, flags(), false), Ok(()));
    let (all_mapped, flush) = table.unmap_region(start, end);
    assert!(all_mapped);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    arena.clear_freed();
    // SAFETY: the range is unmapped and its flush discharged.
    unsafe { table.free_page_table_by_range(start, end) };
    assert!(!arena.freed().is_empty());
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn a_range_still_mapped_keeps_its_tables() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + 8192usize;

    assert_eq!(table.map_region_4k(start, end, frame, flags(), false), Ok(()));
    arena.clear_freed();
    // SAFETY: nothing else walks these tables, and what is still mapped keeps
    // its tables by the sweep's own rule.
    unsafe { table.free_page_table_by_range(start, end) };
    assert!(arena.freed().is_empty());
    assert_eq!(table.phys_addr(start), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn tearing_down_the_children_gives_every_page_back_but_the_root() {
    let (arena, mut table) = table();
    let root = table.root_paddr();
    let built = arena.allocated();

    // SAFETY: nothing runs on these tables but this test, and no other tree
    // links to its subtrees.
    unsafe { table.free_children() };
    let freed = arena.freed();
    assert_eq!(freed.len(), built - 1, "every table below the root");
    assert!(!freed.contains(&root.bits()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn dropping_a_table_frees_its_root() {
    let (arena, table) = table();
    let root = table.root_paddr();
    drop(table);
    assert_eq!(arena.freed(), vec![root.bits()]);
}

#[test]
fn a_leaked_table_frees_nothing() {
    let (arena, table) = table();
    let (_handler, _root) = table.leak();
    assert!(arena.freed().is_empty());
}
