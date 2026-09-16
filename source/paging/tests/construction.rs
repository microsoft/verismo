//! Building a table, and the check that it describes itself.

mod common;

use common::*;
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::PageLevel;
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::ptpage::PTPage;
use paging::{PTEntryFlags, X86Paging};

#[test]
fn direct_mapped_allocator_clones_share_the_allocation_and_deallocation_domain() {
    let arena = Arena::new(ARENA);
    let allocator = Allocator(arena.clone());
    let clone = allocator.clone();
    assert_eq!(allocator.direct_map(), clone.direct_map());
    assert_eq!(allocator.direct_map_base(), clone.direct_map_base());
    let first = allocator.allocate_table_page().unwrap();
    let second = clone.allocate_table_page().unwrap();
    assert_eq!(second, first + 4096);
    assert_eq!(arena.allocated(), 2);
    // SAFETY: neither frame is linked, and both handles share the allocating arena.
    unsafe {
        clone.deallocate_table_page(first);
        allocator.deallocate_table_page(second);
    }
    assert_eq!(arena.freed(), vec![first.bits(), second.bits()]);
    drop(allocator);
    assert_eq!(clone.direct_map_base(), VirtAddr::from(arena.base()));
    drop(clone);
    assert_eq!(std::sync::Arc::strong_count(&arena), 1);
}

#[test]
fn page_allocation_clears_dirty_memory_without_changing_adjacent_frames() {
    let arena = Arena::new(ARENA);
    let allocator = Allocator(arena.clone());
    let before = allocator.allocate_table_page().unwrap();
    let (page, initialized) = PTPage::<X86Paging<Host>, _>::alloc(&allocator).unwrap();
    let after = allocator.allocate_table_page().unwrap();
    assert_eq!(initialized, before + 4096);
    assert_eq!(after, initialized + 4096);
    for index in 0..4096 {
        // SAFETY: all three identity-mapped frames are privately owned and initialized.
        unsafe {
            assert_eq!((before.bits() as *const u8).add(index).read(), 0xff);
            assert_eq!(page.cast::<u8>().add(index).read(), 0);
            assert_eq!((after.bits() as *const u8).add(index).read(), 0xff);
        }
    }
    for frame in [before, initialized, after] {
        // SAFETY: these frames were never linked into a tree.
        unsafe { allocator.deallocate_table_page(frame) };
    }
    assert_eq!(arena.freed().len(), arena.allocated());
}

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
    let root = table.root_paddr();
    assert_eq!(table.phys_addr(VirtAddr::from(root.bits())), Ok(root));
    for child in root_children(&table) {
        assert_eq!(table.phys_addr(VirtAddr::from(child.bits())), Ok(child));
    }
    assert!(arena.allocated() >= 2, "a four-level table needs tables below the root");
    std::mem::forget(table);
}

#[test]
fn a_table_stays_valid_as_it_grows() {
    #[allow(unused_mut)]
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
    let (arena, table) = table();
    #[cfg(feature = "concurrent")]
    let (allocator, content, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let (allocator, root) = table.leak();
    // SAFETY: the root came from the table just leaked, and the allocator is the
    // one that allocated it.
    #[cfg(feature = "concurrent")]
    let table = unsafe { Table::from_root(allocator, content, root) }.expect("its own root");
    #[cfg(not(feature = "concurrent"))]
    let table = unsafe { Table::from_root(allocator, root) }.expect("its own root");
    assert_eq!(table.root_paddr(), root);
    assert_eq!(table.validate_page_table(), Ok(()));
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
    assert_eq!(arena.freed().last(), Some(&root.bits()));
}

#[test]
fn a_root_that_maps_nothing_is_refused() {
    let arena = Arena::new(ARENA);
    let allocator = Allocator(arena.clone());
    let (_, root) = PTPage::<X86Paging<Host>, _>::alloc(&allocator).unwrap();
    // SAFETY: the page was just allocated from this allocator and nothing else
    // holds it. It maps nothing, so the adoption must fail.
    #[cfg(feature = "concurrent")]
    let refused = unsafe { Table::from_root(allocator, WholeTreeLock::default(), root) };
    #[cfg(not(feature = "concurrent"))]
    let refused = unsafe { Table::from_root(allocator, root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    // The root was not freed on rejection: the caller still owns it.
    assert!(arena.freed().is_empty());
}

#[test]
fn a_tree_missing_one_of_its_pages_is_refused() {
    #[allow(unused_mut)]
    let (arena, mut table) = table();
    let child = root_children(&table)[0];
    let (level, flush) = table.unmap(VirtAddr::from(child.bits())).unwrap();
    assert!(level.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    assert_eq!(table.validate_page_table(), Err(PagingError::TablePageNotSelfMapped));
    #[cfg(feature = "concurrent")]
    let (allocator, content, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let (allocator, root) = table.leak();
    // SAFETY: as above; the tree no longer reaches `child`, so it is refused.
    #[cfg(feature = "concurrent")]
    let refused = unsafe { Table::from_root(allocator, content, root) };
    #[cfg(not(feature = "concurrent"))]
    let refused = unsafe { Table::from_root(allocator, root) };
    assert!(matches!(refused, Err(PagingError::TablePageNotSelfMapped)));
    assert!(arena.freed().is_empty());
}

#[test]
fn a_table_can_share_another_ones_top_entries() {
    let (arena, table) = table();
    // SAFETY: both controllers remain alive, only read, and never reclaim shared pages.
    #[cfg(feature = "concurrent")]
    let shared = unsafe {
        Table::new_from_sharing_top::<0, 512>(
            Allocator(arena.clone()),
            WholeTreeLock::default(),
            &table,
        )
    }
    .expect("valid tree");
    #[cfg(not(feature = "concurrent"))]
    let shared = unsafe { Table::new_from_sharing_top::<0, 512>(Allocator(arena.clone()), &table) }
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
    let (_, child) = PTPage::<X86Paging<Host>, _>::alloc(&Allocator(arena.clone())).unwrap();
    // SAFETY: this zeroed subtree is direct-mapped, unlinked, and transferred to the table.
    assert_eq!(unsafe { table.populate(idx, child) }, Ok(true));
    assert_eq!(table.next_table_pa(idx), Some(child));
    // SAFETY: no new installation occurs for the already attached subtree.
    assert_eq!(unsafe { table.populate(idx, child) }, Ok(false));
    table.map_4k(addr, PhysAddr::from(arena.base()), flags(), false).unwrap();
    assert_eq!(table.phys_addr(addr), Ok(PhysAddr::from(arena.base())));
    // SAFETY: every subtree belongs to this inactive table.
    unsafe { table.free_children() };
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
#[cfg_attr(feature = "concurrent", should_panic(expected = "index <"))]
#[cfg_attr(not(feature = "concurrent"), should_panic(expected = "idx <"))]
fn root_inspection_rejects_an_out_of_bounds_index() {
    let (_arena, table) = table();
    table.next_table_pa(512);
}

#[test]
#[cfg_attr(feature = "concurrent", should_panic(expected = "index <"))]
#[cfg_attr(not(feature = "concurrent"), should_panic(expected = "idx <"))]
fn populate_rejects_an_out_of_bounds_index() {
    let (_arena, mut table) = table();
    let child = root_children(&table)[0];
    // SAFETY: the child is live and unaliased; the invalid index must be rejected.
    let _ = unsafe { table.populate(512, child) };
}

#[test]
fn a_five_level_tree_is_deeper_than_a_four_level_one() {
    use paging::level::Lvl;
    use paging::pagetable::PageTable;
    use paging::X86Paging;

    let arena = Arena::new(ARENA);
    #[cfg(feature = "concurrent")]
    let five = PageTable::<X86Paging<Host>, Allocator, Lvl<4>, WholeTreeLock>::new(
        Allocator(arena.clone()),
        WholeTreeLock::default(),
        PTEntryFlags::data(),
    )
    .unwrap();
    #[cfg(not(feature = "concurrent"))]
    let five = PageTable::<X86Paging<Host>, Allocator, Lvl<4>>::new(
        Allocator(arena.clone()),
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
