//! Building a table, and the check that it describes itself.

mod common;

use common::*;
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::PageLevel;
use paging::os_contract::PagingError;
use paging::policy::{RootRange, RootUnion};
use paging::ptpage::PTPage;
use paging::{PTEntryFlags, X86Paging};

#[test]
fn construction_maps_the_direct_map_and_its_own_tables() {
    let (arena, table) = table();
    for offset in [0, 4096, ARENA / 2, ARENA - 4096] {
        let addr = arena.base() + offset;
        assert_eq!(table.phys_addr(VirtAddr::from(addr)), Ok(PhysAddr::from(addr)));
    }
    let root = table.root_paddr();
    assert_eq!(table.phys_addr(VirtAddr::from(root.bits())), Ok(root));
    for child in root_children(&table) {
        assert_eq!(table.phys_addr(VirtAddr::from(child.bits())), Ok(child));
    }
    assert!(arena.allocated() >= 2, "a four-level table needs tables below the root");
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn a_leaked_root_can_be_adopted_again() {
    let (arena, table) = table();
    let (content, root) = table.leak();
    // SAFETY: the root came from the table just leaked.
    let table = unsafe { Table::from_root(content, root) }.expect("its own root");
    assert_eq!(table.root_paddr(), root);
    assert_eq!(table.validate_page_table(), Ok(()));
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
    assert_eq!(arena.freed().last(), Some(&root.bits()));
}

#[test]
fn a_root_that_maps_nothing_is_refused() {
    let arena = Arena::new(ARENA);
    let (_, root) = PTPage::<X86Paging<Host>, Allocator>::alloc().unwrap();
    // SAFETY: the page was just allocated from this allocator and nothing else
    // holds it. It maps nothing, so the adoption must fail.
    let refused = unsafe { Table::from_root(WholeTreeLock::default(), root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    // The root was not freed on rejection: the caller still owns it.
    assert!(arena.freed().is_empty());
}

#[test]
fn a_tree_missing_one_of_its_pages_is_refused() {
    #[allow(unused_mut)]
    let (arena, mut table) = table();
    let child = root_children(&table)[0];
    let (entry, flush) = table.unmap(common::page_4k(VirtAddr::from(child.bits())), true).unwrap();
    assert!(entry.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    assert_eq!(table.validate_page_table(), Err(PagingError::TablePageNotSelfMapped));
    let (content, root) = table.leak();
    // SAFETY: as above; the tree no longer reaches `child`, so it is refused.
    let refused = unsafe { Table::from_root(content, root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    assert!(arena.freed().is_empty());
}

#[test]
fn a_table_can_share_multiple_top_entry_ranges() {
    type Reserved = RootUnion<RootRange<0, 256>, RootRange<256, 512>>;
    let (arena, table) = table();
    let shared =
        unsafe { Table::new_from_sharing_top::<Reserved>(WholeTreeLock::default(), &table) }
            .expect("valid tree");
    for offset in [0, ARENA - 4096] {
        let addr = arena.base() + offset;
        assert_eq!(shared.phys_addr(VirtAddr::from(addr)), Ok(PhysAddr::from(addr)));
    }
    assert_eq!(shared.validate_page_table(), Ok(()));
    assert_eq!(root_children(&shared), root_children(&table));
    std::mem::forget(shared);
    std::mem::forget(table);
}

#[test]
fn populate_reports_what_was_already_there() {
    let (arena, mut table) = table();
    let idx = (0..512).find(|idx| table.next_table_pa(*idx).is_none()).unwrap();
    let addr = VirtAddr::from(idx * PageLevel::Level3.size());
    let (_, child) = PTPage::<X86Paging<Host>, Allocator>::alloc().unwrap();
    // SAFETY: this zeroed subtree is direct-mapped, unlinked, and transferred to the table.
    assert_eq!(unsafe { table.populate(idx, child) }, Ok(true));
    assert_eq!(table.next_table_pa(idx), Some(child));
    // SAFETY: no new installation occurs for the already attached subtree.
    assert_eq!(unsafe { table.populate(idx, child) }, Ok(false));
    table
        .map(common::page_4k(addr), common::frame_4k(PhysAddr::from(arena.base())), flags(), false)
        .unwrap();
    assert_eq!(table.phys_addr(addr), Ok(PhysAddr::from(arena.base())));
    // SAFETY: every subtree belongs to this inactive table.
    unsafe { table.free_children() };
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn a_five_level_tree_is_deeper_than_a_four_level_one() {
    use paging::level::Lvl;
    use paging::pagetable::PageTable;
    use paging::X86Paging;

    let arena = Arena::new(ARENA);
    let five = PageTable::<X86Paging<Host>, Allocator, Lvl<4>, WholeTreeLock>::new(
        WholeTreeLock::default(),
        PTEntryFlags::data(),
    )
    .unwrap();
    assert_eq!(five.validate_page_table(), Ok(()));
    let addr = arena.base();
    assert_eq!(five.phys_addr(VirtAddr::from(addr)), Ok(PhysAddr::from(addr)));
    assert_eq!(
        five.translate(VirtAddr::from(addr)).map(|f| f.size()),
        Ok(PageLevel::Level1.size())
    );
    std::mem::forget(five);
}
