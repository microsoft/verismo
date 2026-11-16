//! Ensures mapping, splitting, and unmapping preserve translations and report page-size and range errors.
#![allow(unused_mut)]

mod common;

use common::*;
use paging::{
    address::{PhysAddr, VirtAddr},
    structs::{Huge, Page, PageLevel, PageSize, PagingError},
};

const SMALL: PageLevel = PageLevel::Level0;
const LARGE: PageLevel = PageLevel::Level1;

#[test]
fn a_mapping_can_be_read_back() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.translate(vaddr).map(|found| found.size()), Ok(SMALL.size()));
    assert_eq!(table.phys_addr(vaddr + 4096usize), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn inclusive_page_range_stops_at_the_last_addressable_page() {
    let page: Page = Page::containing_address(VirtAddr::from(usize::MAX));
    let mut range = Page::range_inclusive(page, page);

    assert_eq!(range.next().map(Page::start_address), Some(page.start_address()));
    assert!(range.next().is_none());
}

#[test]
fn page_range_length_skips_the_noncanonical_address_gap() {
    let low = common::page_4k(VirtAddr::from(0x0000_7fff_ffff_f000usize));
    let high = common::page_4k(VirtAddr::from(0xffff_8000_0000_0000usize));
    let range = Page::range_inclusive(low, high);

    assert_eq!(range.len(), 2);
    assert_eq!(range.count(), 2);
}

#[test]
fn a_large_mapping_covers_the_addresses_inside_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map(common::page_2m(vaddr), common::frame_2m(frame), flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr + 4096usize), Ok(frame + 4096usize));
    assert_eq!(table.translate(vaddr + 4096usize).map(|found| found.size()), Ok(LARGE.size()));
    std::mem::forget(table);
}

#[test]
fn a_second_mapping_is_refused_and_reports_the_existing_level() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let other = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false), Ok(()));
    assert_eq!(
        table.map(common::page_4k(vaddr), common::frame_4k(other), flags(), false),
        Err(PagingError::EntryAlreadyPresent { level: SMALL })
    );
    assert_eq!(table.phys_addr(vaddr), Ok(frame), "the old mapping survived the refusal");
    std::mem::forget(table);
}

#[test]
fn a_mapping_inside_a_large_page_reports_the_large_level() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map(common::page_2m(vaddr), common::frame_2m(frame), flags(), false), Ok(()));
    assert_eq!(
        table.map(common::page_4k(vaddr + 4096usize), common::frame_4k(frame), flags(), false),
        Err(PagingError::EntryAlreadyPresent { level: LARGE })
    );
    std::mem::forget(table);
}

#[test]
fn mapping_a_different_frame_requires_an_unmap_first() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let other = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false), Ok(()));
    let (entry, flush) = table.unmap(common::page_4k(vaddr), Some(true)).unwrap();
    assert!(entry.is_some());
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(other), flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(other));
    std::mem::forget(table);
}

#[test]
fn unmapping_a_small_page_splits_a_larger_mapping() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map(common::page_2m(vaddr), common::frame_2m(frame), flags(), false), Ok(()));
    let (entry, flush) = table.unmap(common::page_4k(vaddr), Some(true)).unwrap();
    assert_eq!(entry.unwrap().leaf_address(SMALL), frame);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
    assert_eq!(table.phys_addr(vaddr + 4096), Ok(frame + 4096));
    std::mem::forget(table);
}

#[test]
fn unmapping_without_split_rejects_a_larger_mapping() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    table.map(common::page_2m(vaddr), common::frame_2m(frame), flags(), false).unwrap();
    assert!(matches!(table.unmap(common::page_4k(vaddr), None), Err(PagingError::WrongPageSize)));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.phys_addr(vaddr + 4096), Ok(frame + 4096));
    std::mem::forget(table);
}

#[test]
fn unmapping_a_large_page_rejects_finer_leaves() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    assert!(matches!(
        table.unmap(common::page_2m(vaddr), Some(true)),
        Err(PagingError::WrongPageSize)
    ));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn splitting_a_large_page_keeps_every_address_it_mapped() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);
    assert_eq!(table.map(common::page_2m(vaddr), common::frame_2m(frame), flags(), false), Ok(()));

    let flush =
        table.set_shared(common::page_4k(vaddr + 4096usize), true).expect("splits the large page");
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
fn split_requires_the_page_type_to_match_the_huge_leaf() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);
    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    assert!(matches!(table.split(common::page_2m(vaddr), true), Err(PagingError::InvalidLevel)));

    let vaddr = vaddr + Huge::SIZE;
    table.map(common::page_2m(vaddr), common::frame_2m(frame), flags(), false).unwrap();
    let flush = table.split(common::page_2m(vaddr), true).unwrap();
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    assert_eq!(table.walk(vaddr).level(), SMALL);
    assert!(matches!(table.split(common::page_2m(vaddr), true), Err(PagingError::InvalidLevel)));
    std::mem::forget(table);
}
