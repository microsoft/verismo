//! Ensures reclamation frees only unused owned tables and fulfills flush obligations without damaging live mappings.
mod common;

use common::{flags, host_flushes, table, Allocator, Arena, Host, Table, ARENA};
use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::X86_64Paging,
    pagetable::KernelPageTable,
    structs::{Lvl, PageLevel, PagingError},
    tlb::MayNeedFlush,
};
use std::collections::BTreeSet;

fn unmap(table: &Table, vaddr: VirtAddr) {
    let (entry, flush) = table.unmap(common::page_4k(vaddr), Some(true)).unwrap();
    assert!(entry.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
}

#[test]
fn freeing_an_address_nothing_mapped_frees_nothing() {
    let (arena, mut table) = table();
    let vaddr = VirtAddr::from(0x80_0000_0000usize);
    assert_eq!(table.free_page_table_by_addr(vaddr, MayNeedFlush::none()), 0);
    assert!(arena.freed().is_empty());
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn point_cleanup_keeps_live_siblings_then_reclaims_the_empty_path() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let first = VirtAddr::from(0x4000_0000usize);
    let second = first + 4096usize;

    let before = arena.allocated();
    for address in [first, second] {
        table.map(common::page_4k(address), common::frame_4k(frame), flags(), false).unwrap();
    }
    let built = arena.allocated() - before;
    unmap(&table, first);

    assert_eq!(table.free_page_table_by_addr(first, MayNeedFlush::none()), 0);
    assert!(arena.freed().is_empty());
    assert_eq!(table.phys_addr(second), Ok(frame));
    let (entry, unmap_flush) = table.unmap(common::page_4k(second), Some(true)).unwrap();
    assert!(entry.is_some());

    let flushes = host_flushes();
    assert_eq!(table.free_page_table_by_addr(second, unmap_flush), built);
    assert_eq!(host_flushes(), flushes + 1);
    assert_eq!(arena.freed().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
    table.map(common::page_4k(first), common::frame_4k(frame), flags(), false).unwrap();
    assert_eq!(table.phys_addr(first), Ok(frame));
}

#[test]
fn a_range_gives_back_the_tables_that_held_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + 8192usize;
    let before = arena.allocated();

    for offset in (0..end - start).step_by(4096) {
        assert_eq!(
            table.map(
                common::page_4k(start + offset),
                common::frame_4k(frame + offset),
                flags(),
                false,
            ),
            Ok(())
        );
    }
    let (all_mapped, flush) = table.unmap_region(start, end).unwrap();
    assert!(all_mapped);

    let built = arena.allocated() - before;
    let flushes = host_flushes();
    assert_eq!(table.cleanup_page_tables_by_range(start, end, flush), built);
    assert_eq!(host_flushes(), flushes + 1);
    assert_eq!(arena.freed().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
}

#[test]
fn range_cleanup_flushes_and_reclaims_many_paths_without_double_free() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let tables = 65;
    let end = start + tables * PageLevel::Level1.size();
    let mut pending = MayNeedFlush::none();
    let before = arena.allocated();

    for offset in (0..end - start).step_by(PageLevel::Level1.size()) {
        let address = start + offset;
        table.map(common::page_4k(address), common::frame_4k(frame), flags(), false).unwrap();
        let (entry, flush) = table.unmap(common::page_4k(address), Some(true)).unwrap();
        assert!(entry.is_some());
        pending = pending.and(flush);
    }

    let built = arena.allocated() - before;
    let flushes = host_flushes();
    let reclaimed = table.cleanup_page_tables_by_range(start, end, pending);
    assert_eq!(reclaimed, built);
    assert!(host_flushes() > flushes);
    let freed = arena.freed();
    assert_eq!(freed.len(), built);
    assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn a_range_still_mapped_keeps_its_tables() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + 8192usize;

    for offset in (0..end - start).step_by(4096) {
        assert_eq!(
            table.map(
                common::page_4k(start + offset),
                common::frame_4k(frame + offset),
                flags(),
                false,
            ),
            Ok(())
        );
    }
    assert_eq!(table.cleanup_page_tables_by_range(start, end, MayNeedFlush::none()), 0);
    assert!(arena.freed().is_empty());
    assert_eq!(table.phys_addr(start), Ok(frame));
    assert_eq!(table.phys_addr(start + 4096), Ok(frame + 4096));
}

#[test]
fn range_cleanup_reaches_sparse_paths_across_one_gib_boundaries() {
    let (arena, mut table) = table();
    let first = VirtAddr::from(0x4c80_0000usize);
    let second = first + 2 * PageLevel::Level2.size();
    let frame = PhysAddr::from(arena.base());
    let before = arena.allocated();
    for addr in [first, second] {
        table.map(common::page_4k(addr), common::frame_4k(frame), flags(), false).unwrap();
        unmap(&table, addr);
    }
    let built = arena.allocated() - before;
    assert_eq!(
        table.cleanup_page_tables_by_range(first, second + 4096, MayNeedFlush::none()),
        built
    );
    assert_eq!(arena.freed().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn range_cleanup_preserves_paths_at_its_exclusive_end() {
    let (arena, mut table) = table();
    let first = VirtAddr::from(0x4000_0000usize);
    let second = first + PageLevel::Level1.size();
    for addr in [first, second] {
        table
            .map(
                common::page_4k(addr),
                common::frame_4k(PhysAddr::from(arena.base())),
                flags(),
                false,
            )
            .unwrap();
        unmap(&table, addr);
    }
    table.cleanup_page_tables_by_range(first, second, MayNeedFlush::none());
    assert_eq!(arena.freed().len(), 1);
    assert_eq!(table.free_page_table_by_addr(second, MayNeedFlush::none()), 3);
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn five_level_path_cleanup_accepts_high_canonical_addresses() {
    let arena = Arena::new(ARENA);
    let mut table = KernelPageTable::<X86_64Paging<Host>, Allocator, Lvl<4>>::new(flags()).unwrap();
    let first = VirtAddr::from(0xffff_8000_4000_0000usize);
    let second = first + 2 * PageLevel::Level2.size();
    let before = arena.allocated();
    for addr in [first, second] {
        table
            .map(
                common::page_4k(addr),
                common::frame_4k(PhysAddr::from(arena.base())),
                flags(),
                false,
            )
            .unwrap();
        let (entry, pending) = table.unmap(common::page_4k(addr), Some(true)).unwrap();
        assert!(entry.is_some());
        // SAFETY: these host-backed tables are never installed.
        unsafe { pending.ignore() };
    }
    let built = arena.allocated() - before;
    let reclaimed = table.free_page_table_by_addr(first, MayNeedFlush::none())
        + table.free_page_table_by_addr(second, MayNeedFlush::none());
    assert_eq!(reclaimed, built);
    assert_eq!(arena.freed().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
#[should_panic(expected = "cleanup range exceeds the root address space")]
fn range_cleanup_rejects_addresses_outside_the_root_span() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0xffff_8000_0000_0000usize);
    table.cleanup_page_tables_by_range(start, start + 4096, MayNeedFlush::none());
}

#[test]
fn explicit_child_teardown_then_drop_frees_each_table_once() {
    let (arena, mut table) = table();
    let address = VirtAddr::from(0x4000_0000usize);
    table
        .map(
            common::page_4k(address),
            common::frame_4k(PhysAddr::from(0x1000usize)),
            flags(),
            false,
        )
        .unwrap();
    let root = table.root_paddr();
    let built = arena.allocated();

    // SAFETY: this inactive tree exclusively owns all of its table pages.
    unsafe { table.free_children() };
    let freed = arena.freed();
    assert_eq!(freed.len(), built - 1, "every table below the root");
    assert!(!freed.contains(&root.bits()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Err(PagingError::NotMapped));
    // SAFETY: the same exclusive ownership and hardware exclusion still hold.
    unsafe { table.free_children() };
    assert_eq!(arena.freed().len(), built - 1);
    drop(table);
    assert_all_tables_freed_once(&arena);
}

#[test]
fn drop_frees_table_pages_but_not_small_or_huge_data_frames() {
    let (arena, table) = table();
    for address in [0x4000_0000usize, 0xffff_8000_4000_0000] {
        table
            .map(
                common::page_4k(VirtAddr::from(address)),
                common::frame_4k(PhysAddr::from(0x1000usize)),
                flags(),
                false,
            )
            .unwrap();
    }
    table
        .map(
            common::page_2m(VirtAddr::from(0x8000_0000usize)),
            common::frame_2m(PhysAddr::from(0x8000_0000usize)),
            flags(),
            false,
        )
        .unwrap();
    drop(table);
    assert_all_tables_freed_once(&arena);
}

#[test]
fn leak_and_adoption_transfer_ownership_of_a_five_level_tree() {
    type Table = KernelPageTable<X86_64Paging<Host>, Allocator, Lvl<4>>;
    let arena = Arena::new(ARENA);
    let table = Table::new(flags()).unwrap();
    let address = VirtAddr::from(0xffff_8000_4000_0000usize);
    let frame = PhysAddr::from(0x1000usize);
    table.map(common::page_4k(address), common::frame_4k(frame), flags(), false).unwrap();
    let root = table.leak();
    assert!(arena.freed().is_empty());
    // SAFETY: leak transferred this allocator-owned, inactive tree without aliases.
    let adopted = unsafe { Table::from_root(root) }.unwrap();
    assert_eq!(adopted.phys_addr(address), Ok(frame));
    assert_eq!(adopted.validate_page_table(), Ok(()));
    drop(adopted);
    assert_all_tables_freed_once(&arena);
}

fn assert_all_tables_freed_once(arena: &Arena) {
    let freed = arena.freed();
    let expected: BTreeSet<_> =
        (0..arena.allocated()).map(|index| arena.base() + index * 4096).collect();
    assert_eq!(freed.len(), expected.len());
    assert_eq!(freed.into_iter().collect::<BTreeSet<_>>(), expected);
}
