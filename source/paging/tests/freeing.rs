//! Giving table pages back: the path sweep, the range sweep, and teardown.

mod common;

use std::collections::BTreeSet;
use std::sync::Arc;

use common::*;
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::{LevelSpec, Lvl, PageLevel};
use paging::os_contract::PagingError;
use paging::pagetable::PageTable;
use paging::X86Paging;

/// Unmaps `vaddr` and discharges the flush, which the freeing needs.
fn unmap(table: &mut Table, vaddr: VirtAddr) {
    let (entry, flush) = table.unmap(common::page_4k(vaddr), true).unwrap();
    assert!(entry.is_some());
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

    assert_eq!(table.map(common::page_4k(first), common::frame_4k(frame), flags(), false), Ok(()));
    assert_eq!(table.map(common::page_4k(second), common::frame_4k(frame), flags(), false), Ok(()));
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
    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false), Ok(()));
    let built = arena.allocated() - before;
    assert_eq!(built, 3, "a four-level tree needs three tables below the root");

    unmap(&mut table, vaddr);
    // SAFETY: `vaddr` is unmapped and its flush discharged.
    assert_eq!(unsafe { table.free_page_table_by_addr(vaddr) }, built);
    assert_eq!(arena.freed().len(), built);

    // What is left still describes itself, and still works.
    assert_eq!(table.validate_page_table(), Ok(()));
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn a_range_gives_back_the_tables_that_held_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + (2 * 1024 * 1024usize);

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
    arena.clear_freed();
    // SAFETY: nothing else walks these tables, and what is still mapped keeps
    // its tables by the sweep's own rule.
    unsafe { table.free_page_table_by_range(start, end) };
    assert!(arena.freed().is_empty());
    assert_eq!(table.phys_addr(start), Ok(frame));
    std::mem::forget(table);
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
        unmap(&mut table, addr);
    }
    let built = arena.allocated() - before;
    // SAFETY: these unaliased tables are inactive and their leaf flushes discharged.
    unsafe { table.free_page_table_by_range(first, second + 4096) };
    assert_eq!(arena.freed().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn range_cleanup_keeps_its_exclusive_end_and_ignores_empty_ranges() {
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
        unmap(&mut table, addr);
    }
    // SAFETY: these inactive paths are unaliased and all leaf flushes discharged.
    unsafe { table.free_page_table_by_range(first, first) };
    assert!(arena.freed().is_empty());
    unsafe { table.free_page_table_by_range(first, second) };
    assert_eq!(arena.freed().len(), 1);
    assert_eq!(unsafe { table.free_page_table_by_addr(second) }, 3);
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn five_level_range_cleanup_uses_high_canonical_offsets_without_wrapping() {
    use paging::level::Lvl;
    use paging::pagetable::PageTable;
    use paging::X86Paging;

    let arena = Arena::new(ARENA);
    let mut table = PageTable::<X86Paging<Host>, Allocator, Lvl<4>, WholeTreeLock>::new(
        WholeTreeLock::default(),
        flags(),
    )
    .unwrap();
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
        let (entry, pending) = table.unmap(common::page_4k(addr), true).unwrap();
        assert!(entry.is_some());
        // SAFETY: these host-backed tables are never installed.
        unsafe { pending.ignore() };
    }
    let built = arena.allocated() - before;
    // SAFETY: the empty paths belong solely to this inactive tree.
    unsafe { table.free_page_table_by_range(first, second + 4096) };
    assert_eq!(arena.freed().len(), built);
    assert_eq!(table.validate_page_table(), Ok(()));
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
fn dropping_a_table_frees_its_root_and_descendants() {
    let (arena, table) = table();
    let root = table.root_paddr();
    drop(table);
    assert_all_tables_freed_once(&arena);
    assert_eq!(arena.freed().last(), Some(&root.bits()));
}

#[test]
fn a_leaked_table_frees_nothing() {
    let (arena, table) = table();
    let (_content, _root) = table.leak();
    assert!(arena.freed().is_empty());
}

fn assert_all_tables_freed_once(arena: &Arena) {
    let freed = arena.freed();
    let expected: BTreeSet<_> =
        (0..arena.allocated()).map(|index| arena.base() + index * 4096).collect();
    assert_eq!(freed.len(), expected.len());
    assert_eq!(freed.into_iter().collect::<BTreeSet<_>>(), expected);
}

type Owned<L> = PageTable<X86Paging<Host>, Allocator, L, WholeTreeLock>;
type Content = WholeTreeLock;

fn owned<L: LevelSpec>() -> (Arc<Arena>, Owned<L>) {
    let arena = Arena::new(ARENA);
    let table = Owned::new(WholeTreeLock::default(), flags()).unwrap();
    (arena, table)
}

fn parts<L: LevelSpec>(table: Owned<L>) -> (Content, PhysAddr) {
    table.leak()
}

unsafe fn adopt<L: LevelSpec>(content: Content, root: PhysAddr) -> Owned<L> {
    unsafe { Owned::from_root(content, root) }.unwrap()
}

macro_rules! owned_drop_tests {
    ($module:ident, $fixture:ident, $parts:ident, $adopt:ident, $level:ty) => {
        #[allow(unused_mut)]
        mod $module {
            use super::*;

            #[test]
            fn drop_recursively_frees_tables_but_not_small_or_huge_data_frames() {
                let (arena, mut table) = $fixture::<$level>();
                let root = table.root_paddr();
                let small_frame = PhysAddr::from(0x1000usize);
                let huge_frame = PhysAddr::from(0x8000_0000usize);
                for address in [0x4000_0000usize, 0xffff_8000_4000_0000] {
                    table
                        .map(
                            common::page_4k(VirtAddr::from(address)),
                            common::frame_4k(small_frame),
                            flags(),
                            false,
                        )
                        .unwrap();
                    assert_eq!(table.phys_addr(VirtAddr::from(address)), Ok(small_frame));
                }
                table
                    .map(
                        common::page_2m(VirtAddr::from(0x8000_0000usize)),
                        common::frame_2m(huge_frame),
                        flags(),
                        false,
                    )
                    .unwrap();
                assert!(arena.allocated() > <$level>::DEPTH + 1);
                assert!(arena.freed().is_empty());
                drop(table);
                assert_all_tables_freed_once(&arena);
                assert_eq!(arena.freed().last(), Some(&root.bits()));
                assert!(!arena.freed().contains(&small_frame.bits()));
                assert!(!arena.freed().contains(&huge_frame.bits()));
                assert_eq!(Arc::strong_count(&arena), 1);
            }

            #[test]
            fn leak_transfers_the_tree_without_freeing_then_adoption_owns_all_pages() {
                let (arena, mut table) = $fixture::<$level>();
                let address = VirtAddr::from(0xffff_8000_4000_0000usize);
                let frame = PhysAddr::from(0x1000usize);
                table
                    .map(common::page_4k(address), common::frame_4k(frame), flags(), false)
                    .unwrap();
                let root = table.root_paddr();
                assert_eq!(Arc::strong_count(&arena), 1);
                let (content, leaked_root) = $parts(table);
                assert_eq!(leaked_root, root);
                assert_eq!(Arc::strong_count(&arena), 1);
                assert!(arena.freed().is_empty());
                // SAFETY: leak transfers this allocator-owned, inactive tree without aliases.
                let adopted = unsafe { $adopt::<$level>(content, leaked_root) };
                assert_eq!(adopted.root_paddr(), root);
                assert_eq!(adopted.phys_addr(address), Ok(frame));
                assert_eq!(adopted.validate_page_table(), Ok(()));
                drop(adopted);
                assert_all_tables_freed_once(&arena);
                assert_eq!(arena.freed().last(), Some(&root.bits()));
                assert_eq!(Arc::strong_count(&arena), 1);
            }

            #[test]
            fn explicit_child_teardown_then_drop_never_frees_a_table_twice() {
                let (arena, mut table) = $fixture::<$level>();
                table
                    .map(
                        common::page_4k(VirtAddr::from(0x4000_0000usize)),
                        common::frame_4k(PhysAddr::from(0x1000usize)),
                        flags(),
                        false,
                    )
                    .unwrap();
                let root = table.root_paddr();
                let allocated = arena.allocated();
                // SAFETY: this inactive tree exclusively owns all of its table pages.
                unsafe { table.free_children() };
                assert_eq!(arena.freed().len(), allocated - 1);
                assert!(!arena.freed().contains(&root.bits()));
                unsafe { table.free_children() };
                assert_eq!(arena.freed().len(), allocated - 1);
                drop(table);
                assert_all_tables_freed_once(&arena);
                assert_eq!(arena.freed().last(), Some(&root.bits()));
            }
        }
    };
}

owned_drop_tests!(selected_four_level, owned, parts, adopt, Lvl<3>);
owned_drop_tests!(selected_five_level, owned, parts, adopt, Lvl<4>);
