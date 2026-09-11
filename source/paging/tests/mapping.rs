//! Mapping, refusing to remap, splitting, and unmapping.

mod common;

use common::*;
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::PageLevel;
use paging::os_contract::PagingError;

const SMALL: PageLevel = PageLevel::Level0;
const LARGE: PageLevel = PageLevel::Level1;

#[test]
fn a_mapping_can_be_read_back() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.translate(vaddr).map(|found| found.size()), Ok(SMALL.size()));
    assert_eq!(table.phys_addr(vaddr + 4096usize), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn a_large_mapping_covers_the_addresses_inside_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_2m(vaddr, frame, flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr + 4096usize), Ok(frame + 4096usize));
    assert_eq!(table.translate(vaddr + 4096usize).map(|found| found.size()), Ok(LARGE.size()));
    std::mem::forget(table);
}

#[test]
fn a_second_mapping_is_refused_and_says_what_is_there() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let other = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    assert_eq!(
        table.map_4k(vaddr, other, flags(), false),
        Err(PagingError::EntryAlreadyPresent { frame, level: SMALL })
    );
    assert_eq!(table.phys_addr(vaddr), Ok(frame), "the old mapping survived the refusal");
    std::mem::forget(table);
}

#[test]
fn a_mapping_inside_a_large_page_is_refused_with_the_frame_it_would_have_hidden() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_2m(vaddr, frame, flags(), false), Ok(()));
    assert_eq!(
        table.map_4k(vaddr + 4096usize, frame, flags(), false),
        Err(PagingError::EntryAlreadyPresent { frame: frame + 4096usize, level: LARGE })
    );
    std::mem::forget(table);
}

#[test]
fn remapping_needs_an_unmap_first() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let other = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    let (entry, flush) = table.unmap_4k(vaddr);
    assert!(entry.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    assert_eq!(table.map_4k(vaddr, other, flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(other));
    std::mem::forget(table);
}

#[test]
fn unmapping_at_the_wrong_size_leaves_the_mapping_alone() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_2m(vaddr, frame, flags(), false), Ok(()));
    let (entry, flush) = table.unmap_4k(vaddr);
    assert!(entry.is_none(), "a 2 MiB page is not a 4 KiB one");
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn splitting_a_large_page_keeps_every_address_it_mapped() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);
    assert_eq!(table.map_2m(vaddr, frame, flags(), false), Ok(()));

    let flush = table.set_shared_4k(vaddr + 4096usize).expect("splits the large page");
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    assert_eq!(table.translate(vaddr + 4096usize).map(|found| found.size()), Ok(SMALL.size()));
    for page in 0..512usize {
        let inside = vaddr + page * 4096;
        assert_eq!(table.phys_addr(inside), Ok(frame + page * 4096), "page {page}");
    }
    std::mem::forget(table);
}

#[test]
fn a_region_maps_in_the_largest_pages_it_can() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + (4 * 1024 * 1024usize);

    assert_eq!(table.map_region(start, end, frame, flags()), Ok(()));
    assert_eq!(table.translate(start).map(|found| found.size()), Ok(LARGE.size()));
    for offset in [0usize, 4096, 2 * 1024 * 1024, 4 * 1024 * 1024 - 4096] {
        assert_eq!(table.phys_addr(start + offset), Ok(frame + offset), "offset {offset:#x}");
    }
    assert_eq!(table.phys_addr(end), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn widening_a_direct_map_steps_over_what_it_already_maps() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(arena.base());
    let wider = start + (4 * ARENA);

    assert_eq!(table.map_region_if_absent(start, wider, frame, flags()), Ok(()));
    for offset in [0usize, 4096, ARENA - 4096, ARENA, 4 * ARENA - 4096] {
        assert_eq!(table.phys_addr(start + offset), Ok(frame + offset), "offset {offset:#x}");
    }
    // Doing it again finds everything already there.
    assert_eq!(table.map_region_if_absent(start, wider, frame, flags()), Ok(()));
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn widening_onto_someone_elses_mapping_is_refused() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(arena.base());
    let elsewhere = PhysAddr::from(arena.base() + ARENA);

    assert!(matches!(
        table.map_region_if_absent(start, start + ARENA, elsewhere, flags()),
        Err(PagingError::EntryAlreadyPresent { .. })
    ));
    std::mem::forget(table);
}

#[test]
fn a_region_can_be_unmapped_whatever_sizes_map_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + (2 * 1024 * 1024 + 8192usize);

    assert_eq!(table.map_region(start, end, frame, flags()), Ok(()));
    let (all_mapped, flush) = table.unmap_region(start, end);
    assert!(all_mapped);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    for offset in [0usize, 4096, 2 * 1024 * 1024, 2 * 1024 * 1024 + 4096] {
        assert_eq!(table.phys_addr(start + offset), Err(PagingError::NotMapped));
    }
    // The arena it was built over is untouched.
    assert_eq!(table.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn unmapping_what_was_never_mapped_says_so() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let (all_mapped, flush) = table.unmap_region(start, start + 8192usize);
    assert!(!all_mapped);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    std::mem::forget(table);
}
