//! Ensures constructed and imported roots map their own table pages before controllers can use them.
mod common;

use common::*;
use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{PTEntryFlags, X86_64Paging},
    structs::{NoRootEntries, PTPage, PTPageTree, PageLevel, PagingError, UserPolicy},
};

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
    let root = table.leak();
    // SAFETY: the root came from the table just leaked.
    let table = unsafe { Table::from_root(root) }.expect("its own root");
    assert_eq!(table.root_paddr(), root);
    assert_eq!(table.validate_page_table(), Ok(()));
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
    assert_eq!(arena.freed().last(), Some(&root.bits()));
}

#[test]
fn a_root_that_maps_nothing_is_refused() {
    let arena = Arena::new(ARENA);
    let (_, root) = PTPage::<X86_64Paging<Host>, Allocator>::alloc().unwrap();
    // SAFETY: the page was just allocated from this allocator and nothing else
    // holds it. It maps nothing, so the adoption must fail.
    let refused = unsafe { Table::from_root(root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    // The root was not freed on rejection: the caller still owns it.
    assert!(arena.freed().is_empty());
}

#[test]
fn a_tree_missing_one_of_its_pages_is_refused() {
    #[allow(unused_mut)]
    let (arena, mut table) = table();
    let child = root_children(&table)[0];
    let (entry, flush) =
        table.unmap(common::page_4k(VirtAddr::from(child.bits())), Some(true)).unwrap();
    assert!(entry.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    assert_eq!(table.validate_page_table(), Err(PagingError::TablePageNotSelfMapped));
    let root = table.leak();
    // SAFETY: as above; the tree no longer reaches `child`, so it is refused.
    let refused = unsafe { Table::from_root(root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    assert!(arena.freed().is_empty());
}

#[test]
fn a_table_can_share_multiple_top_entry_ranges() {
    type Reserved = NoRootEntries;
    let (arena, table) = table();
    // SAFETY: the source tree remains live until after the returned test table.
    let shared =
        unsafe { Table::new_from_sharing_top::<UserPolicy<Reserved>, _, _, _>(&table, |k| k) }
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
fn populate_transfers_an_owned_subtree() {
    let (arena, mut table) = table();
    let idx = (0..512).find(|idx| table.next_table_pa(*idx).is_none()).unwrap();
    let addr = VirtAddr::from(idx * PageLevel::Level3.size());
    let (_, child) = PTPage::<X86_64Paging<Host>, Allocator>::alloc().unwrap();
    // SAFETY: this zeroed child-level tree is unlinked and exclusively owned.
    let subtree = unsafe { PTPageTree::from_owned_root(child) };
    assert!(table.populate_owned(idx, subtree).is_ok());
    assert_eq!(table.next_table_pa(idx), Some(child));
    let (_, rejected) = PTPage::<X86_64Paging<Host>, Allocator>::alloc().unwrap();
    // SAFETY: this zeroed child-level tree is unlinked and exclusively owned.
    let rejected = unsafe { PTPageTree::from_owned_root(rejected) };
    let rejected = match table.populate_owned(idx, rejected) {
        Err(error) if error.error == PagingError::NotLeafEntry => error.subtree,
        _ => panic!("occupied root entry accepted another subtree"),
    };
    table
        .map(common::page_4k(addr), common::frame_4k(PhysAddr::from(arena.base())), flags(), false)
        .unwrap();
    assert_eq!(table.phys_addr(addr), Ok(PhysAddr::from(arena.base())));
    // SAFETY: every subtree belongs to this inactive table.
    unsafe { table.free_children() };
    drop(table);
    drop(rejected);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn a_five_level_tree_is_deeper_than_a_four_level_one() {
    use paging::{arch::x86_64::X86_64Paging, pagetable::KernelPageTable, structs::Lvl};

    let arena = Arena::new(ARENA);
    let five = KernelPageTable::<X86_64Paging<Host>, Allocator, Lvl<4>>::new(PTEntryFlags::data())
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
