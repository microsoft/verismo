//! Building a table, and the check that it describes itself.

mod common;

use common::*;
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::PageLevel;
use paging::os_contract::{DirectMappedPagingHandler, PagingError};
use paging::PTEntryFlags;

#[test]
fn new_maps_the_whole_arena() {
    let (arena, table) = table();
    for offset in [0, 4096, ARENA / 2, ARENA - 4096] {
        let addr = arena.base() + offset;
        assert_eq!(table.phys_addr(VirtAddr::from(addr)), Ok(PhysAddr::from(addr)));
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn new_reaches_its_own_table_pages() {
    let (arena, table) = table();
    assert_eq!(table.root_vaddr(), VirtAddr::from(table.root_paddr().bits()));
    for child in root_children(&table) {
        assert_eq!(table.phys_addr(VirtAddr::from(child.bits())), Ok(child));
    }
    assert!(arena.allocated() >= 2, "a four-level table needs tables below the root");
    std::mem::forget(table);
}

#[test]
fn a_table_stays_valid_as_it_grows() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    for page in 0..64usize {
        let vaddr = VirtAddr::from(0x4000_0000 + page * 4096);
        assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    }
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn a_leaked_root_can_be_adopted_again() {
    let (_arena, table) = table();
    let (handler, root) = table.leak();
    // SAFETY: the root came from the table just leaked, and the handler is the
    // one that allocated it.
    let table = unsafe { Table::from_root(handler, root) }.expect("its own root");
    assert_eq!(table.root_paddr(), root);
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn a_root_that_maps_nothing_is_refused() {
    let arena = Arena::new(ARENA);
    let handler = Handler(arena.clone());
    let root = handler.allocate_table_page().unwrap();
    // SAFETY: the page was just allocated from this handler and nothing else
    // holds it. It maps nothing, so the adoption must fail.
    let refused = unsafe { Table::from_root(handler, root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    // The root was not freed on rejection: the caller still owns it.
    assert!(arena.freed().is_empty());
}

#[test]
fn a_tree_missing_one_of_its_pages_is_refused() {
    let (arena, mut table) = table();
    let child = root_children(&table)[0];
    let (level, flush) = table.unmap(VirtAddr::from(child.bits()));
    assert!(level.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    assert_eq!(table.validate_page_table(), Err(PagingError::TablePageNotSelfMapped));
    let (handler, root) = table.leak();
    // SAFETY: as above; the tree no longer reaches `child`, so it is refused.
    let refused = unsafe { Table::from_root(handler, root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    assert!(arena.freed().is_empty());
}

#[test]
fn a_table_can_share_another_ones_top_entries() {
    let (arena, table) = table();
    let top = 0..512;
    let shared =
        Table::new_from_sharing_top(Handler(arena.clone()), &table, top).expect("valid tree");
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
    let idx = (0..512).find(|idx| table.next_table_pa(*idx).is_some()).unwrap();
    let child = table.next_table_pa(idx).unwrap();
    assert_eq!(table.populate(idx, child), Ok(false));

    let free = (0..512).find(|idx| table.next_table_pa(*idx).is_none()).unwrap();
    assert_eq!(table.populate(free, child), Ok(true));
    assert_eq!(table.next_table_pa(free), Some(child));
    let _ = arena;
    std::mem::forget(table);
}

#[test]
fn a_five_level_tree_is_deeper_than_a_four_level_one() {
    use paging::level::Lvl;
    use paging::pagetable::PageTable;
    use paging::X86Paging;

    let arena = Arena::new(ARENA);
    let five = PageTable::<X86Paging<Host>, Handler, Lvl<4>>::new(
        Handler(arena.clone()),
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
