//! Mapping, rejecting occupied addresses, splitting, and unmapping.
#![cfg_attr(feature = "concurrent", allow(unused_mut))]

mod common;

use common::*;
#[cfg(not(feature = "concurrent"))]
use core::ops::Range;
use paging::address::{PhysAddr, VirtAddr};
use paging::frame::PhysFrame;
use paging::level::PageLevel;
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
#[cfg(not(feature = "concurrent"))]
use paging::os_contract::DirectMappedAllocator;
use paging::os_contract::PagingError;
use paging::page::Page;
#[cfg(not(feature = "concurrent"))]
use paging::pagetable::PageTable;
use paging::sizes::PageOffset;
use paging::PTEntryFlags;
#[cfg(not(feature = "concurrent"))]
use paging::{level::Lvl, X86Paging};
#[cfg(not(feature = "concurrent"))]
use std::sync::atomic::{AtomicUsize, Ordering};

const SMALL: PageLevel = PageLevel::Level0;
const LARGE: PageLevel = PageLevel::Level1;

struct Size8KiB;

impl PageOffset for Size8KiB {
    const SHIFT: usize = 13;
}

#[cfg(not(feature = "concurrent"))]
struct BudgetAllocator;
#[cfg(not(feature = "concurrent"))]
static ALLOCATION_BUDGET: AtomicUsize = AtomicUsize::new(usize::MAX);

#[cfg(not(feature = "concurrent"))]
unsafe impl DirectMappedAllocator for BudgetAllocator {
    fn direct_map() -> (Range<PhysAddr>, VirtAddr) {
        Allocator::direct_map()
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        ALLOCATION_BUDGET
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |left| left.checked_sub(1))
            .map_err(|_| PagingError::AllocFrame)?;
        <Allocator as DirectMappedAllocator>::allocate_table_page()
    }

    unsafe fn deallocate_table_page(page: PhysAddr) {
        // SAFETY: ownership is forwarded unchanged to the original allocator.
        unsafe { <Allocator as DirectMappedAllocator>::deallocate_table_page(page) };
    }
}

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
fn an_unsupported_typed_page_size_is_rejected() {
    let (_arena, mut table) = table();
    let page = Page::<Size8KiB>::from_start_address(VirtAddr::from(0x4000_0000usize)).unwrap();
    let frame =
        PhysFrame::<Size8KiB>::from_start_address(PhysAddr::from(0x8000_0000usize)).unwrap();

    assert_eq!(table.map(page, frame, flags(), false), Err(PagingError::InvalidLevel));
    assert!(matches!(table.unmap(page, true), Err(PagingError::InvalidLevel)));
    assert!(matches!(table.set_flags(page, flags(), true), Err(PagingError::InvalidLevel)));
    std::mem::forget(table);
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
    let (entry, flush) = table.unmap(common::page_4k(vaddr), true).unwrap();
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
    let (entry, flush) = table.unmap(common::page_4k(vaddr), true).unwrap();
    assert_eq!(entry.unwrap().leaf_address(SMALL), frame);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
    assert_eq!(table.phys_addr(vaddr + 4096), Ok(frame + 4096));
    std::mem::forget(table);
}

#[test]
fn unmapping_a_large_page_rejects_finer_leaves() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let vaddr = VirtAddr::from(0x4000_0000usize);

    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    assert!(matches!(table.unmap(common::page_2m(vaddr), true), Err(PagingError::NotLeafEntry)));
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
fn region_mapping_rejects_a_misaligned_physical_start() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + 4096usize;
    let phys = PhysAddr::from(0x2001usize);

    assert_eq!(table.map_region(start, end, phys, flags()), Err(PagingError::InvalidAddress));
    assert_eq!(table.phys_addr(start), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn region_mapping_rejects_misaligned_virtual_bounds() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0001usize);
    let end = start + 4096usize;

    assert_eq!(table.map_region(start, end, frame, flags()), Err(PagingError::InvalidRange));
    std::mem::forget(table);
}

#[test]
#[cfg(not(feature = "concurrent"))]
fn failed_mapping_growth_reclaims_its_private_preparation() {
    let arena = Arena::new(ARENA);
    ALLOCATION_BUDGET.store(usize::MAX, Ordering::Relaxed);
    let mut table = PageTable::<X86Paging<Host>, BudgetAllocator, Lvl<3>>::new(flags()).unwrap();
    let vaddr = VirtAddr::from(0x4000_0000usize);
    let frame = PhysAddr::from(arena.base());
    let before = arena.allocated();
    let original_level = table.walk(vaddr).level();

    ALLOCATION_BUDGET.store(1, Ordering::Relaxed);
    assert_eq!(
        table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false),
        Err(PagingError::AllocFrame)
    );
    assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
    assert_eq!(table.walk(vaddr).level(), original_level);
    assert_eq!(arena.allocated(), before + 1);
    assert_eq!(arena.freed().len(), 1);

    ALLOCATION_BUDGET.store(3, Ordering::Relaxed);
    assert_eq!(table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false), Ok(()));
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.validate_page_table(), Ok(()));
    std::mem::forget(table);
}

#[test]
fn region_mapping_near_the_address_end_does_not_overflow_large_page_lookahead() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(usize::MAX & !(LARGE.size() - 1));
    let end = start + SMALL.size();
    let frame = PhysAddr::from(arena.base());

    assert_eq!(table.map_region(start, end, frame, flags()), Ok(()));
    assert_eq!(table.phys_addr(start), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn region_mapping_does_not_advance_physical_address_past_usize_end() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + SMALL.size();
    let frame = PhysAddr::from(usize::MAX & !(SMALL.size() - 1));

    assert_eq!(table.map_region(start, end, frame, flags()), Ok(()));
    std::mem::forget(table);
}

#[test]
fn physical_range_overflow_is_rejected_before_mapping() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + 2 * SMALL.size();
    let frame = PhysAddr::from(usize::MAX & !(SMALL.size() - 1));

    assert_eq!(table.map_region(start, end, frame, flags()), Err(PagingError::InvalidRange));
    assert_eq!(table.phys_addr(start), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn region_mapping_rejects_non_present_flags() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);

    assert_eq!(
        table.map_region(
            start,
            start + SMALL.size(),
            PhysAddr::from(arena.base()),
            PTEntryFlags::WRITABLE,
        ),
        Err(PagingError::InvalidFlags)
    );
    assert_eq!(table.phys_addr(start), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn region_mapping_rejects_an_identical_existing_mapping() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + ARENA;

    assert_eq!(table.map_region(start, end, frame, flags()), Ok(()));
    assert!(matches!(
        table.map_region(start, end, frame, flags()),
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
    let (all_mapped, flush) = table.unmap_region(start, end).unwrap();
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
fn a_partial_gib_range_keeps_two_mib_leaves() {
    const TWO_MIB: usize = 2 * 1024 * 1024;
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let frame = PhysAddr::from(0x4_0000_0000usize);

    table.map(common::page_1g(start), common::frame_1g(frame), flags(), false).unwrap();
    let before = arena.allocated();
    let (all_mapped, flush) = table.unmap_region(start + TWO_MIB, start + 3 * TWO_MIB).unwrap();
    assert!(all_mapped);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };

    assert_eq!(arena.allocated(), before + 1);
    assert_eq!(table.walk(start).level(), PageLevel::Level1);
    assert_eq!(table.phys_addr(start), Ok(frame));
    assert_eq!(table.phys_addr(start + TWO_MIB), Err(PagingError::NotMapped));
    assert_eq!(table.phys_addr(start + 2 * TWO_MIB), Err(PagingError::NotMapped));
    assert_eq!(table.phys_addr(start + 3 * TWO_MIB), Ok(frame + 3 * TWO_MIB));
    std::mem::forget(table);
}

#[test]
fn unmapping_what_was_never_mapped_says_so() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let (all_mapped, flush) = table.unmap_region(start, start + 8192usize).unwrap();
    assert!(!all_mapped);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    std::mem::forget(table);
}
