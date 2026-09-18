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
use paging::os_contract::{MapRegionError, PagingError};
use paging::page::Page;
#[cfg(not(feature = "concurrent"))]
use paging::pagetable::PageTable;
use paging::sizes::{PageOffset, PageSize, Size1GiB, Size2MiB, Size4KiB};
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
fn page_ranges_iterate_in_address_order() {
    let start = common::page_4k(VirtAddr::from(0x4000usize));
    let end = common::page_4k(VirtAddr::from(0x7000usize));
    let frame = common::frame_4k(PhysAddr::from(0x8000usize));
    assert_eq!((start + 2).start_address(), VirtAddr::from(0x6000usize));
    assert_eq!(end - start, 3);
    assert_eq!(start.pt_index(), 4);
    assert_eq!((frame + 2).start_address(), PhysAddr::from(0xa000usize));

    let exclusive: Vec<_> = Page::range(start, end).map(Page::start_address).collect();
    assert_eq!(
        exclusive,
        [VirtAddr::from(0x4000usize), VirtAddr::from(0x5000usize), VirtAddr::from(0x6000usize)]
    );

    let inclusive: Vec<_> = Page::range_inclusive(start, end).map(Page::start_address).collect();
    assert_eq!(
        inclusive,
        [
            VirtAddr::from(0x4000usize),
            VirtAddr::from(0x5000usize),
            VirtAddr::from(0x6000usize),
            VirtAddr::from(0x7000usize),
        ]
    );
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
fn a_fixed_two_mib_region_uses_two_mib_leaves() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + (4 * 1024 * 1024usize);
    let range =
        Page::range_inclusive(common::page_2m(start), common::page_2m(end - Size2MiB::SIZE));
    let mut frames =
        (0..range.len()).map(|offset| common::frame_2m(frame + offset * Size2MiB::SIZE));

    assert_eq!(table.map_region(range, &mut frames, flags()), Ok(()));
    assert_eq!(table.translate(start).map(|found| found.size()), Ok(LARGE.size()));
    for offset in [0usize, 4096, 2 * 1024 * 1024, 4 * 1024 * 1024 - 4096] {
        assert_eq!(table.phys_addr(start + offset), Ok(frame + offset), "offset {offset:#x}");
    }
    assert_eq!(table.phys_addr(end), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn an_aligned_one_gib_region_uses_a_one_gib_leaf() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(Size1GiB::SIZE);
    let end = start + Size1GiB::SIZE;
    let frame = PhysAddr::from(2 * Size1GiB::SIZE);
    let range = Page::range_inclusive(common::page_1g(start), common::page_1g(start));
    let mut frames = core::iter::once(common::frame_1g(frame));

    assert_eq!(table.map_region(range, &mut frames, flags()), Ok(()));
    assert_eq!(table.translate(start).map(|found| found.size()), Ok(Size1GiB::SIZE));
    assert_eq!(table.phys_addr(end - Size4KiB::SIZE), Ok(frame + Size1GiB::SIZE - Size4KiB::SIZE));
    std::mem::forget(table);
}

#[test]
fn region_mapping_rejects_an_unsupported_page_size() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let range = Page::range_inclusive(
        Page::<Size8KiB>::from_start_address(start).unwrap(),
        Page::<Size8KiB>::from_start_address(start).unwrap(),
    );
    let mut frames = core::iter::once(
        PhysFrame::<Size8KiB>::from_start_address(PhysAddr::from(arena.base())).unwrap(),
    );

    assert_eq!(
        table.map_region(range, &mut frames, flags()),
        Err(MapRegionError { error: PagingError::InvalidLevel, unmapped_pages: 2 })
    );
    assert_eq!(table.phys_addr(start), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn region_mapping_rejects_an_empty_inclusive_range() {
    let (_arena, mut table) = table();
    let start = common::page_4k(VirtAddr::from(0x4000_1000usize));
    let end = common::page_4k(VirtAddr::from(0x4000_0000usize));
    let mut frames = core::iter::empty();

    assert_eq!(
        table.map_region(Page::range_inclusive(start, end), &mut frames, flags()),
        Err(MapRegionError { error: PagingError::InvalidRange, unmapped_pages: 0 })
    );
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
fn region_mapping_accepts_the_last_aligned_virtual_page() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(usize::MAX & !(LARGE.size() - 1));
    let frame = PhysAddr::from(arena.base());
    let range = Page::range_inclusive(common::page_4k(start), common::page_4k(start));
    let mut frames = core::iter::once(common::frame_4k(frame));

    assert_eq!(table.map_region(range, &mut frames, flags()), Ok(()));
    assert_eq!(table.phys_addr(start), Ok(frame));
    std::mem::forget(table);
}

#[test]
fn region_mapping_accepts_the_last_physical_frame() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let frame = PhysAddr::from(usize::MAX & !(SMALL.size() - 1));
    let range = Page::range_inclusive(common::page_4k(start), common::page_4k(start));
    let mut frames = core::iter::once(common::frame_4k(frame));

    assert_eq!(table.map_region(range, &mut frames, flags()), Ok(()));
    std::mem::forget(table);
}

#[test]
fn exhausted_frame_iterator_reports_the_unmapped_suffix() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + 2 * SMALL.size();
    let range = common::range_4k(start, end);
    let mut frames = core::iter::once(common::frame_4k(PhysAddr::from(arena.base())));

    assert_eq!(
        table.map_region(range, &mut frames, flags()),
        Err(MapRegionError { error: PagingError::InvalidRange, unmapped_pages: 1 })
    );
    assert_eq!(table.phys_addr(start), Ok(PhysAddr::from(arena.base())));
    assert_eq!(table.phys_addr(start + SMALL.size()), Err(PagingError::NotMapped));
    std::mem::forget(table);
}

#[test]
fn seam_crossing_exhaustion_reports_one_unmapped_page() {
    let (arena, mut table) = table();
    let low = common::page_4k(VirtAddr::from(0x0000_7fff_ffff_f000usize));
    let high = common::page_4k(VirtAddr::from(0xffff_8000_0000_0000usize));
    let frame = PhysAddr::from(arena.base());
    let mut frames = core::iter::once(common::frame_4k(frame));

    assert_eq!(
        table.map_region(Page::range_inclusive(low, high), &mut frames, flags()),
        Err(MapRegionError { error: PagingError::InvalidRange, unmapped_pages: 1 })
    );
    assert_eq!(table.phys_addr(low.start_address()), Ok(frame));
    assert_eq!(table.phys_addr(high.start_address()), Err(PagingError::NotMapped));

    std::mem::forget(table);
}

#[test]
fn region_mapping_accepts_noncontiguous_frames_and_leaves_extras() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let frame_base = PhysAddr::from(arena.base());
    let expected = [frame_base, frame_base + 3 * SMALL.size(), frame_base + SMALL.size()];
    let extra = common::frame_4k(frame_base + 7 * SMALL.size());
    let mut frames = expected.map(common::frame_4k).into_iter().chain(core::iter::once(extra));

    assert_eq!(
        table.map_region(common::range_4k(start, start + 3 * SMALL.size()), &mut frames, flags()),
        Ok(())
    );
    for (offset, frame) in expected.into_iter().enumerate() {
        assert_eq!(table.phys_addr(start + offset * SMALL.size()), Ok(frame));
    }
    assert_eq!(frames.next().map(|frame| frame.start_address()), Some(extra.start_address()));

    std::mem::forget(table);
}

#[test]
fn mixed_region_maps_either_adjacent_order() {
    for four_k_first in [false, true] {
        let (arena, mut table) = table();
        let two_mib_start = VirtAddr::from(0x4040_0000usize);
        let range_2m =
            Page::range_inclusive(common::page_2m(two_mib_start), common::page_2m(two_mib_start));
        let range_4k = if four_k_first {
            common::range_4k(two_mib_start - 2 * SMALL.size(), two_mib_start)
        } else {
            common::range_4k(
                two_mib_start + Size2MiB::SIZE,
                two_mib_start + Size2MiB::SIZE + 2 * SMALL.size(),
            )
        };
        let frame_2m = PhysAddr::from(arena.base());
        let frame_4k = frame_2m + 2 * Size2MiB::SIZE;
        let mut frames_2m = core::iter::once(common::frame_2m(frame_2m));
        let mut frames_4k = common::contiguous_frames_4k(frame_4k, range_4k.len());

        assert_eq!(
            table.map_region_mixed(range_2m, &mut frames_2m, range_4k, &mut frames_4k, flags(),),
            Ok(())
        );
        assert_eq!(table.phys_addr(two_mib_start), Ok(frame_2m));
        assert_eq!(table.phys_addr(range_4k.start.start_address()), Ok(frame_4k));

        std::mem::forget(table);
    }
}

#[test]
fn mixed_region_treats_the_canonical_seam_as_adjacent() {
    let (arena, mut table) = table();
    let low = common::page_2m(VirtAddr::from(0x0000_7fff_ffe0_0000usize));
    let high = common::page_4k(VirtAddr::from(0xffff_8000_0000_0000usize));
    let frame_2m = PhysAddr::from(arena.base());
    let frame_4k = frame_2m + Size2MiB::SIZE;
    let mut frames_2m = core::iter::once(common::frame_2m(frame_2m));
    let mut frames_4k = core::iter::once(common::frame_4k(frame_4k));

    assert_eq!(
        table.map_region_mixed(
            Page::range_inclusive(low, low),
            &mut frames_2m,
            Page::range_inclusive(high, high),
            &mut frames_4k,
            flags(),
        ),
        Ok(())
    );
    assert_eq!(table.phys_addr(low.start_address()), Ok(frame_2m));
    assert_eq!(table.phys_addr(high.start_address()), Ok(frame_4k));

    std::mem::forget(table);
}

#[test]
fn mixed_region_rejects_nonadjacent_ranges_without_consuming_frames() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4040_0000usize);
    let range_2m = Page::range_inclusive(common::page_2m(start), common::page_2m(start));
    let range_4k =
        common::range_4k(start + Size2MiB::SIZE + SMALL.size(), start + Size2MiB::SIZE + 8192);
    let frame_2m = common::frame_2m(PhysAddr::from(arena.base()));
    let frame_4k = common::frame_4k(PhysAddr::from(arena.base()) + Size2MiB::SIZE);
    let mut frames_2m = core::iter::once(frame_2m);
    let mut frames_4k = core::iter::once(frame_4k);

    assert_eq!(
        table.map_region_mixed(range_2m, &mut frames_2m, range_4k, &mut frames_4k, flags(),),
        Err(MapRegionError { error: PagingError::InvalidRange, unmapped_pages: 513 })
    );
    assert_eq!(frames_2m.next().map(|frame| frame.start_address()), Some(frame_2m.start_address()));
    assert_eq!(frames_4k.next().map(|frame| frame.start_address()), Some(frame_4k.start_address()));

    std::mem::forget(table);
}

#[test]
fn region_mapping_rejects_non_present_flags() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let range = Page::range_inclusive(common::page_4k(start), common::page_4k(start));
    let mut frames = core::iter::once(common::frame_4k(PhysAddr::from(arena.base())));

    assert_eq!(
        table.map_region(range, &mut frames, PTEntryFlags::WRITABLE),
        Err(MapRegionError { error: PagingError::InvalidFlags, unmapped_pages: 1 })
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

    assert_eq!(map_region_4k!(table, start, end, frame, flags()), Ok(()));
    assert!(matches!(
        map_region_4k!(table, start, end, frame, flags()),
        Err(failure) if matches!(failure.error, PagingError::EntryAlreadyPresent { .. })
    ));
    std::mem::forget(table);
}

#[test]
fn failed_region_mapping_reports_the_unmapped_suffix() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let split = start + PageLevel::Level1.size();
    let end = split + 2 * Size4KiB::SIZE;
    let frame = PhysAddr::from(arena.base());
    let occupied_frame = frame + 3 * PageLevel::Level1.size();

    table
        .map(
            common::page_4k(split + Size4KiB::SIZE),
            common::frame_4k(occupied_frame),
            flags(),
            false,
        )
        .unwrap();
    assert_eq!(
        map_region_4k!(table, start, end, frame, flags()),
        Err(MapRegionError {
            error: PagingError::EntryAlreadyPresent { level: PageLevel::Level0 },
            unmapped_pages: 2,
        })
    );
    assert_eq!(table.phys_addr(start), Ok(frame));
    assert_eq!(table.phys_addr(split), Err(PagingError::NotMapped));
    assert_eq!(table.phys_addr(split + Size4KiB::SIZE), Ok(occupied_frame));
    std::mem::forget(table);
}

#[test]
fn mixed_region_failure_counts_the_untouched_second_range() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4040_0000usize);
    let range_2m = Page::range_inclusive(common::page_2m(start), common::page_2m(start));
    let range_4k =
        common::range_4k(start + Size2MiB::SIZE, start + Size2MiB::SIZE + 2 * SMALL.size());
    let frame = PhysAddr::from(arena.base());
    assert_eq!(map_at!(table, start, frame, PageLevel::Level1, flags(), false), Ok(()));
    let mut frames_2m = core::iter::once(common::frame_2m(frame + Size2MiB::SIZE));
    let mut frames_4k = common::contiguous_frames_4k(frame + 2 * Size2MiB::SIZE, range_4k.len());

    assert_eq!(
        table.map_region_mixed(range_2m, &mut frames_2m, range_4k, &mut frames_4k, flags(),),
        Err(MapRegionError {
            error: PagingError::EntryAlreadyPresent { level: PageLevel::Level1 },
            unmapped_pages: 514,
        })
    );

    std::mem::forget(table);
}

#[test]
fn mixed_region_failure_after_first_range_keeps_that_range() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(0x4040_0000usize);
    let four_k_start = start + Size2MiB::SIZE;
    let range_2m = Page::range_inclusive(common::page_2m(start), common::page_2m(start));
    let range_4k = common::range_4k(four_k_start, four_k_start + SMALL.size());
    let frame = PhysAddr::from(arena.base());
    assert_eq!(map_at!(table, four_k_start, frame, PageLevel::Level0, flags(), false), Ok(()));
    let mut frames_2m = core::iter::once(common::frame_2m(frame + Size2MiB::SIZE));
    let mut frames_4k = core::iter::once(common::frame_4k(frame + 2 * Size2MiB::SIZE));

    assert_eq!(
        table.map_region_mixed(range_2m, &mut frames_2m, range_4k, &mut frames_4k, flags(),),
        Err(MapRegionError {
            error: PagingError::EntryAlreadyPresent { level: PageLevel::Level0 },
            unmapped_pages: 1,
        })
    );
    assert_eq!(table.phys_addr(start), Ok(frame + Size2MiB::SIZE));

    std::mem::forget(table);
}

#[test]
fn a_region_can_be_unmapped_whatever_sizes_map_it() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let start = VirtAddr::from(0x4000_0000usize);
    let end = start + (2 * 1024 * 1024 + 8192usize);

    let range_2m = Page::range_inclusive(common::page_2m(start), common::page_2m(start));
    let mut frames_2m = core::iter::once(common::frame_2m(frame));
    let range_4k = common::range_4k(start + Size2MiB::SIZE, end);
    let mut frames_4k = common::contiguous_frames_4k(frame + Size2MiB::SIZE, range_4k.len());
    assert_eq!(
        table.map_region_mixed(range_2m, &mut frames_2m, range_4k, &mut frames_4k, flags(),),
        Ok(())
    );
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
