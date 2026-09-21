//! Canonical-boundary range protection regressions.

mod common;

use common::{flags, table};
use paging::address::{PhysAddr, VirtAddr};
use paging::level::PageLevel;
use paging::os_contract::PagingError;
use paging::PTEntryFlags;

const PAGE: usize = 4096;
const LOW_CANONICAL_END: usize = 1usize << 47;

fn readonly() -> PTEntryFlags {
    PTEntryFlags::PRESENT | PTEntryFlags::NX
}

fn discharge<T: paging::tlb::TlbFlush>(pending: paging::tlb::MayNeedFlush<T>) {
    // SAFETY: these host-backed tables are never installed in hardware.
    unsafe { pending.ignore() };
}

#[test]
fn exclusive_low_canonical_end_succeeds_without_touching_high_memory() {
    let (arena, table) = table();
    let low = VirtAddr::from(LOW_CANONICAL_END - PAGE);
    let large = VirtAddr::from(LOW_CANONICAL_END - 2 * 1024 * 1024);
    let high = VirtAddr::from(LOW_CANONICAL_END);
    map_at!(table, large, PhysAddr::from(arena.base()), PageLevel::Level1, flags(), false).unwrap();
    table
        .map(common::page_4k(high), common::frame_4k(PhysAddr::from(arena.base())), flags(), false)
        .unwrap();

    let (result, pending) = table.set_flags_range(low, high, readonly(), true);

    assert_eq!(result, Ok(()));
    discharge(pending);
    assert!(table.walk(large).read().writable());
    assert!(!table.walk(low).read().writable());
    assert!(table.walk(high).read().writable());
}

#[test]
fn cross_gap_range_updates_both_canonical_segments() {
    let (arena, table) = table();
    let low = VirtAddr::from(LOW_CANONICAL_END - PAGE);
    let high = VirtAddr::from(LOW_CANONICAL_END);
    table
        .map(common::page_4k(low), common::frame_4k(PhysAddr::from(arena.base())), flags(), false)
        .unwrap();
    table
        .map(
            common::page_4k(high),
            common::frame_4k(PhysAddr::from(arena.base() + PAGE)),
            flags(),
            false,
        )
        .unwrap();

    let (result, pending) = table.set_flags_range(low, high + PAGE, readonly(), true);

    assert_eq!(result, Ok(()));
    discharge(pending);
    assert!(!table.walk(low).read().writable());
    assert!(!table.walk(high).read().writable());
}

#[test]
fn cross_gap_range_reports_an_unmapped_high_segment_after_the_valid_prefix() {
    let (arena, table) = table();
    let low = VirtAddr::from(LOW_CANONICAL_END - PAGE);
    let high = VirtAddr::from(LOW_CANONICAL_END);
    table
        .map(common::page_4k(low), common::frame_4k(PhysAddr::from(arena.base())), flags(), false)
        .unwrap();

    let (result, pending) = table.set_flags_range(low, high + PAGE, readonly(), true);

    assert_eq!(result, Err(PagingError::NotMapped));
    discharge(pending);
    assert!(!table.walk(low).read().writable());
    assert_eq!(table.phys_addr(high), Err(PagingError::NotMapped));
}
