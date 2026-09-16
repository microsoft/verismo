//! Mapping, rejecting occupied addresses, splitting, and unmapping.
#![cfg_attr(feature = "concurrent", allow(unused_mut))]

mod common;

use common::*;
#[cfg(not(feature = "concurrent"))]
use core::ops::Range;
use paging::address::{PhysAddr, VirtAddr};
use paging::level::PageLevel;
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
#[cfg(not(feature = "concurrent"))]
use paging::os_contract::DirectMappedAllocator;
use paging::os_contract::PagingError;
#[cfg(not(feature = "concurrent"))]
use paging::pagetable::PageTable;
#[cfg(not(feature = "concurrent"))]
use paging::{level::Lvl, X86Paging};
#[cfg(not(feature = "concurrent"))]
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(not(feature = "concurrent"))]
use std::sync::Arc;

const SMALL: PageLevel = PageLevel::Level0;
const LARGE: PageLevel = PageLevel::Level1;

#[cfg(not(feature = "concurrent"))]
#[derive(Clone)]
struct BudgetAllocator {
    inner: Allocator,
    remaining: Arc<AtomicUsize>,
}

#[cfg(not(feature = "concurrent"))]
unsafe impl DirectMappedAllocator for BudgetAllocator {
    fn direct_map(&self) -> Range<PhysAddr> {
        self.inner.direct_map()
    }

    fn direct_map_base(&self) -> VirtAddr {
        self.inner.direct_map_base()
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        self.remaining
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |left| left.checked_sub(1))
            .map_err(|_| PagingError::AllocFrame)?;
        self.inner.allocate_table_page()
    }

    unsafe fn deallocate_table_page(&self, page: PhysAddr) {
        // SAFETY: ownership is forwarded unchanged to the original allocator.
        unsafe { self.inner.deallocate_table_page(page) };
    }
}

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
fn mapping_a_different_frame_requires_an_unmap_first() {
    let (arena, mut table) = table();
    let frame = PhysAddr::from(arena.base());
    let other = PhysAddr::from(arena.base() + 4096);
    let vaddr = VirtAddr::from(0x4000_0000usize);

    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
    let (entry, flush) = table.unmap_4k(vaddr).unwrap();
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
    let (entry, flush) = table.unmap_4k(vaddr).unwrap();
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

    let flush = table.set_shared_4k(vaddr + 4096usize, true).expect("splits the large page");
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
#[cfg(not(feature = "concurrent"))]
fn failed_mapping_growth_reclaims_its_private_preparation() {
    let arena = Arena::new(ARENA);
    let remaining = Arc::new(AtomicUsize::new(usize::MAX));
    let allocator =
        BudgetAllocator { inner: Allocator(arena.clone()), remaining: remaining.clone() };
    let mut table =
        PageTable::<X86Paging<Host>, BudgetAllocator, Lvl<3>>::new(allocator, flags()).unwrap();
    let vaddr = VirtAddr::from(0x4000_0000usize);
    let frame = PhysAddr::from(arena.base());
    let before = arena.allocated();
    let original_level = table.walk(vaddr).level();

    remaining.store(1, Ordering::Relaxed);
    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Err(PagingError::AllocFrame));
    assert_eq!(table.phys_addr(vaddr), Err(PagingError::NotMapped));
    assert_eq!(table.walk(vaddr).level(), original_level);
    assert_eq!(arena.allocated(), before + 1);
    assert_eq!(arena.freed().len(), 1);

    remaining.store(3, Ordering::Relaxed);
    assert_eq!(table.map_4k(vaddr, frame, flags(), false), Ok(()));
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
fn widening_near_the_address_end_uses_a_nonwrapping_boundary() {
    let (arena, mut table) = table();
    let start = VirtAddr::from(usize::MAX & !(LARGE.size() - 1));
    let end = start + SMALL.size();
    let frame = PhysAddr::from(arena.base());

    assert_eq!(table.map_region_if_absent(start, end, frame, flags()), Ok(()));
    assert_eq!(table.map_region_if_absent(start, end, frame, flags()), Ok(()));
    assert_eq!(table.phys_addr(start), Ok(frame));
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
fn unmapping_what_was_never_mapped_says_so() {
    let (_arena, mut table) = table();
    let start = VirtAddr::from(0x4000_0000usize);
    let (all_mapped, flush) = table.unmap_region(start, start + 8192usize).unwrap();
    assert!(!all_mapped);
    // SAFETY: nothing runs on these tables but this test.
    unsafe { flush.ignore() };
    std::mem::forget(table);
}
