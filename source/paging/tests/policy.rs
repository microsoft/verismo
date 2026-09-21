//! Shared kernel subtrees remain readable, immutable, and owned by their source.

mod common;

use std::collections::BTreeSet;
use std::mem::size_of;
use std::ops::Range;
use std::sync::Arc;

use common::{Allocator, Arena, Host, WholeTreeLock, ARENA};
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::level::{Lvl, PageLevel};
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::LockSpec;
use paging::pagetable::{KernelPageTable, UserPageTable};
use paging::policy::{PagingOwnershipPolicy, RootRange, UserPolicy};
use paging::sizes::entry_index;
use paging::tlb::{MayNeedFlush, TlbFlush};
use paging::{PTEntryFlags, X86Paging};

const PAGE: usize = 4096;
const LARGE: usize = 2 * 1024 * 1024;
const TOP_SIZE: usize = 512 * 1024 * 1024 * 1024;
const KERNEL_START: usize = 1;
const KERNEL_END: usize = 511;
const SMALL_LEVEL: PageLevel = PageLevel::Level0;
const LARGE_LEVEL: PageLevel = PageLevel::Level1;

type Arch = X86Paging<Host>;
type Reserved<const START: usize, const END: usize> = RootRange<START, END>;
type Table = KernelPageTable<Arch, Allocator, Lvl<3>, WholeTreeLock>;
type User<'kernel, const START: usize, const END: usize> =
    UserPageTable<'kernel, Arch, Allocator, Lvl<3>, WholeTreeLock, Reserved<START, END>>;

fn fixture() -> (Arc<Arena>, Table, WholeTreeLock) {
    let arena = Arena::new(ARENA);
    let locks = WholeTreeLock::default();
    let table = Table::new(locks.clone(), common::flags()).unwrap();
    (arena, table, locks)
}

fn user<'kernel, const START: usize, const END: usize>(
    arena: &Arc<Arena>,
    kernel: &'kernel Table,
    locks: &WholeTreeLock,
) -> User<'kernel, START, END> {
    assert_direct_map_in::<START, END>(arena);
    unsafe { Table::new_from_sharing_top::<Reserved<START, END>>(locks.clone(), kernel) }.unwrap()
}

fn leak<const START: usize, const END: usize>(
    user: User<'_, START, END>,
) -> (UserPolicy<'_, Reserved<START, END>>, PhysAddr) {
    let (_locks, policy, root) = user.leak();
    (policy, root)
}

fn kernel_top(arena: &Arena) -> Range<usize> {
    assert_direct_map_in::<KERNEL_START, KERNEL_END>(arena);
    KERNEL_START..KERNEL_END
}

fn assert_direct_map_in<const START: usize, const END: usize>(arena: &Arena) {
    for address in [arena.base(), arena.base() + arena.len() - 1] {
        let index = entry_index(VirtAddr::from(address), PageLevel::Level3);
        assert!((START..END).contains(&index));
    }
}

fn direct_map_index(arena: &Arena) -> usize {
    entry_index(VirtAddr::from(arena.base()), PageLevel::Level3)
}

fn reserved_hole(arena: &Arena) -> usize {
    if direct_map_index(arena) == KERNEL_START {
        KERNEL_START + 1
    } else {
        KERNEL_START
    }
}

fn readonly() -> PTEntryFlags {
    PTEntryFlags::PRESENT | PTEntryFlags::NX
}

fn assert_readonly(entry: PTEntry<Arch>) {
    assert!(entry.flags().contains(readonly()));
    assert!(!entry.writable());
}

fn discharge<T: TlbFlush>(pending: MayNeedFlush<T>) {
    // SAFETY: these host-backed tables are never installed.
    unsafe { pending.ignore() };
}

fn assert_error<T>(result: Result<T, PagingError>, expected: PagingError) {
    match result {
        Err(error) => assert_eq!(error, expected),
        Ok(_) => panic!("operation unexpectedly succeeded; expected {expected:?}"),
    }
}

fn assert_reclaimed(arena: &Arena) {
    let freed = arena.freed();
    assert_eq!(freed.len(), arena.allocated());
    assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), freed.len());
}

macro_rules! assert_range_error {
    ($table:expr, $start:expr, $end:expr, $frame:expr, $error:expr) => {{
        let (start, end, frame, error) = ($start, $end, $frame, $error);
        let flushes = common::host_flushes();
        assert_error(
            map_region_4k!($table, start, end, frame, common::flags())
                .map_err(|failure| failure.error),
            error,
        );
        assert_error($table.unmap_region(start, end), error);
        let (result, pending) = $table.set_flags_range(start, end, readonly(), true);
        assert_eq!(result, Err(error));
        pending.expect_no_flush();
        assert_eq!(common::host_flushes(), flushes, "preflight flushed a forbidden range");
    }};
}

macro_rules! policy_tests {
    ($module:ident, $fixture:path, $share:ident, $leak:path) => {
        #[allow(unused_mut)]
        mod $module {
            use super::*;

            #[test]
            fn shared_reads_preserve_copied_entries_and_all_reserved_entries_are_non_owned() {
                let (arena, mut kernel, locks) = $fixture();
                let empty = reserved_hole(&arena);
                assert!(kernel.next_table_pa(direct_map_index(&arena)).is_some());
                assert_eq!(kernel.next_table_pa(empty), None);
                let kernel_pages = arena.allocated();
                let user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                assert_ne!(user.root_paddr(), kernel.root_paddr());
                assert_eq!(arena.allocated(), kernel_pages + 1);
                for index in 0..512 {
                    assert_eq!(user.next_table_pa(index), kernel.next_table_pa(index));
                }
                for offset in [0, PAGE, ARENA / 2, ARENA - PAGE] {
                    let addr = VirtAddr::from(arena.base() + offset);
                    assert_eq!(user.phys_addr(addr), Ok(PhysAddr::from(addr.bits())));
                    assert_eq!(user.translate(addr).unwrap().size(), LARGE);
                    assert_eq!(user.walk(addr).read().raw(), kernel.walk(addr).read().raw());
                }
                assert_eq!(user.validate_page_table(), Ok(()));
                drop(user);
                // SAFETY: the user root is gone and the inactive kernel tree is unaliased.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn different_const_bounds_grant_different_private_root_entries() {
                let (arena, mut kernel, locks) = $fixture();
                let mut wide = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let mut narrow = $share::<2, 510>(&arena, &kernel, &locks);
                let frame = PhysAddr::from(arena.base());
                for index in [KERNEL_START, KERNEL_END - 1] {
                    let addr = VirtAddr::from(index * TOP_SIZE);
                    assert_eq!(kernel.next_table_pa(index), None);
                    let allocated = arena.allocated();
                    let acquired = locks.acquisitions();
                    assert_error(
                        wide.map(
                            common::page_4k(addr),
                            common::frame_4k(frame),
                            common::flags(),
                            false,
                        ),
                        PagingError::PermissionDenied,
                    );
                    assert_eq!(arena.allocated(), allocated);
                    assert_eq!(locks.acquisitions(), acquired);
                    narrow
                        .map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false)
                        .unwrap();
                    assert_eq!(narrow.phys_addr(addr), Ok(frame));
                    assert_eq!(wide.phys_addr(addr), Err(PagingError::NotMapped));
                    assert_eq!(kernel.phys_addr(addr), Err(PagingError::NotMapped));
                }
                assert_eq!(narrow.validate_page_table(), Ok(()));
                assert_eq!(wide.validate_page_table(), Ok(()));
                // SAFETY: only the narrower controller owns these inactive private descendants.
                unsafe {
                    narrow.free_children();
                    wide.free_children();
                }
                drop(narrow);
                drop(wide);
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn every_point_mutation_rejects_shared_mappings_and_protected_holes() {
                let (arena, mut kernel, locks) = $fixture();
                let shared_index = direct_map_index(&arena);
                let empty = reserved_hole(&arena);
                assert_eq!(kernel.next_table_pa(empty), None);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let allocated = arena.allocated();
                let acquired = locks.acquisitions();
                let frame = PhysAddr::from(arena.base());
                let kernel_addr = VirtAddr::from(arena.base());
                let leaf = kernel.walk(kernel_addr).read().raw();
                let root_child = kernel.next_table_pa(shared_index);
                assert!(root_child.is_some());
                for addr in [
                    kernel_addr,
                    VirtAddr::from(shared_index * TOP_SIZE),
                    VirtAddr::from(empty * TOP_SIZE),
                ] {
                    let denied = PagingError::PermissionDenied;
                    assert_error(
                        map_at!(user, addr, frame, SMALL_LEVEL, common::flags(), false),
                        denied,
                    );
                    assert_error(
                        user.map_with_parent_flags(
                            common::page_4k(addr),
                            common::frame_4k(frame),
                            common::flags(),
                            false,
                            PTEntryFlags::PRESENT,
                        ),
                        denied,
                    );
                    assert_error(
                        user.map(
                            common::page_4k(addr),
                            common::frame_4k(frame),
                            common::flags(),
                            false,
                        ),
                        denied,
                    );
                    assert_error(
                        user.map(
                            common::page_2m(addr),
                            common::frame_2m(frame),
                            common::flags(),
                            false,
                        ),
                        denied,
                    );
                    assert_error(split_at!(user, addr, SMALL_LEVEL, true), denied);
                    assert_error(set_flags_at!(user, addr, SMALL_LEVEL, readonly(), true), denied);
                    assert_error(user.set_shared(common::page_4k(addr), true), denied);
                    assert_error(user.set_private(common::page_4k(addr), true), denied);
                    assert_error(user.unmap(common::page_4k(addr), true), denied);
                    assert_error(unmap_at!(user, addr, SMALL_LEVEL), denied);
                    assert_error(user.unmap(common::page_4k(addr), true), denied);
                    assert_error(user.unmap(common::page_2m(addr), true), denied);
                    assert_eq!(arena.allocated(), allocated);
                    assert_eq!(locks.acquisitions(), acquired);
                    assert_eq!(kernel.walk(kernel_addr).read().raw(), leaf);
                    assert_eq!(user.walk(kernel_addr).read().raw(), leaf);
                    assert_eq!(user.next_table_pa(shared_index), root_child);
                    assert_eq!(user.next_table_pa(empty), None);
                    assert!(arena.freed().is_empty());
                }
                drop(user);
                // SAFETY: no user root or hardware retains this tree.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn every_range_mutation_preflights_shared_and_empty_reserved_entries() {
                let (arena, mut kernel, locks) = $fixture();
                let empty = reserved_hole(&arena);
                assert_eq!(kernel.next_table_pa(empty), None);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let allocated = arena.allocated();
                let acquired = locks.acquisitions();
                let frame = PhysAddr::from(arena.base());
                let leaf = kernel.walk(VirtAddr::from(arena.base())).read().raw();
                for start in [VirtAddr::from(arena.base()), VirtAddr::from(empty * TOP_SIZE)] {
                    assert_range_error!(
                        user,
                        start,
                        start + LARGE,
                        frame,
                        PagingError::PermissionDenied
                    );
                    assert_eq!(arena.allocated(), allocated);
                    assert_eq!(locks.acquisitions(), acquired);
                    assert_eq!(kernel.walk(VirtAddr::from(arena.base())).read().raw(), leaf);
                    assert_eq!(user.next_table_pa(empty), None);
                }
                drop(user);
                // SAFETY: the source is now the sole inactive owner.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn boundary_rejection_never_maps_unmaps_or_protects_a_private_prefix() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let start = VirtAddr::from(top.start * TOP_SIZE - LARGE);
                let boundary = start + LARGE;
                let frame = PhysAddr::from(arena.base());
                for mapped in [false, true] {
                    if mapped {
                        user.map(
                            common::page_2m(start),
                            common::frame_2m(frame),
                            common::flags(),
                            false,
                        )
                        .unwrap();
                    }
                    let entry = user.walk(start).read().raw();
                    let allocated = arena.allocated();
                    let acquired = locks.acquisitions();
                    assert_range_error!(
                        user,
                        start,
                        boundary + LARGE,
                        frame,
                        PagingError::PermissionDenied
                    );
                    assert_eq!(user.walk(start).read().raw(), entry);
                    assert_eq!(
                        user.phys_addr(start),
                        if mapped { Ok(frame) } else { Err(PagingError::NotMapped) }
                    );
                    assert_eq!(arena.allocated(), allocated);
                    assert_eq!(locks.acquisitions(), acquired);
                }
                let (result, pending) = user.set_flags_range(start, boundary, readonly(), true);
                assert_eq!(result, Ok(()));
                discharge(pending);
                assert_readonly(user.walk(start).read());
                let (mapped, pending) = user.unmap_region(start, boundary).unwrap();
                assert!(mapped);
                discharge(pending);
                map_region_4k!(user, start, boundary, frame, common::flags()).unwrap();
                assert_eq!(kernel.phys_addr(start), Err(PagingError::NotMapped));
                assert_eq!(
                    kernel.phys_addr(VirtAddr::from(arena.base())),
                    Ok(PhysAddr::from(arena.base()))
                );
                // SAFETY: cleanup only reclaims this inactive user's private descendants.
                unsafe { user.free_children() };
                drop(user);
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn reversed_ranges_fail_without_mutation_for_both_policies() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let start = VirtAddr::from(top.start * TOP_SIZE);
                let frame = PhysAddr::from(arena.base());
                let allocated = arena.allocated();
                let acquired = locks.acquisitions();
                assert_range_error!(kernel, start + LARGE, start, frame, PagingError::InvalidRange);
                assert_eq!(arena.allocated(), allocated);
                assert_eq!(locks.acquisitions(), acquired);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let allocated = arena.allocated();
                assert_range_error!(user, start + LARGE, start, frame, PagingError::InvalidRange);
                assert_eq!(arena.allocated(), allocated);
                assert_eq!(locks.acquisitions(), acquired);
                drop(user);
                // SAFETY: no shared roots remain and the kernel is inactive.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn empty_ranges_in_protected_entries_are_no_ops() {
                let (arena, mut kernel, locks) = $fixture();
                let empty = reserved_hole(&arena);
                assert_eq!(kernel.next_table_pa(empty), None);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let allocated = arena.allocated();
                let acquired = locks.acquisitions();
                for addr in [VirtAddr::from(arena.base()), VirtAddr::from(empty * TOP_SIZE)] {
                    let (mapped, pending) = user.unmap_region(addr, addr).unwrap();
                    assert!(mapped);
                    pending.expect_no_flush();
                    let (result, pending) = user.set_flags_range(addr, addr, readonly(), true);
                    assert_eq!(result, Ok(()));
                    pending.expect_no_flush();
                }
                assert_eq!(arena.allocated(), allocated);
                assert_eq!(locks.acquisitions(), acquired);
                assert!(arena.freed().is_empty());
                drop(user);
                // SAFETY: the inactive kernel is the sole remaining controller.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn multiple_shared_subtrees_and_reserved_holes_remain_non_owned() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let first = direct_map_index(&arena);
                let second = reserved_hole(&arena);
                let empty = top.clone().find(|index| *index != first && *index != second).unwrap();
                let addr = VirtAddr::from(second * TOP_SIZE);
                let frame = PhysAddr::from(arena.base());
                assert_eq!(kernel.next_table_pa(second), None);
                kernel
                    .map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false)
                    .unwrap();
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                assert!(user.next_table_pa(first).is_some());
                assert!(user.next_table_pa(second).is_some());
                assert_eq!(user.next_table_pa(first), kernel.next_table_pa(first));
                assert_eq!(user.next_table_pa(second), kernel.next_table_pa(second));
                assert_eq!(user.next_table_pa(empty), None);
                assert_eq!(user.phys_addr(addr), Ok(frame));
                assert_eq!(user.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
                // SAFETY: neither inactive shared subtree belongs to the user controller.
                unsafe { user.free_children() };
                assert!(arena.freed().is_empty());
                assert_eq!(user.next_table_pa(first), kernel.next_table_pa(first));
                assert_eq!(user.next_table_pa(second), kernel.next_table_pa(second));
                drop(user);
                // SAFETY: both borrowed subtrees now belong exclusively to the inactive kernel.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn private_user_subtrees_do_not_alias_unshared_kernel_mappings() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let private_index = top.end;
                let addr = VirtAddr::from(private_index * TOP_SIZE);
                let frame = PhysAddr::from(arena.base());
                kernel
                    .map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false)
                    .unwrap();
                let kernel_leaf = kernel.walk(addr).read().raw();
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let root = user.root_paddr();
                assert_eq!(user.phys_addr(addr), Err(PagingError::NotMapped));
                assert_eq!(user.next_table_pa(private_index), None);
                let allocated = arena.allocated();
                user.map(
                    common::page_4k(addr),
                    common::frame_4k(frame + PAGE),
                    common::flags(),
                    false,
                )
                .unwrap();
                let private_pages = arena.allocated() - allocated;
                assert_ne!(user.next_table_pa(private_index), kernel.next_table_pa(private_index));
                discharge(set_flags_at!(user, addr, SMALL_LEVEL, readonly(), true).unwrap());
                assert_eq!(user.phys_addr(addr), Ok(frame + PAGE));
                assert_eq!(kernel.phys_addr(addr), Ok(frame));
                assert_eq!(kernel.walk(addr).read().raw(), kernel_leaf);
                discharge(user.unmap(common::page_4k(addr), true).unwrap().1);
                // SAFETY: the private mapping is gone and its flush obligation discharged.
                assert_eq!(unsafe { user.free_page_table_by_addr(addr) }, private_pages);
                assert_eq!(arena.freed().len(), private_pages);
                assert!(arena.freed().iter().all(|page| *page > root.bits()));
                assert_eq!(user.next_table_pa(private_index), None);
                assert_eq!(kernel.walk(addr).read().raw(), kernel_leaf);
                assert_eq!(user.validate_page_table(), Ok(()));
                drop(user);
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn private_mappings_support_all_mapping_editing_and_unmapping_variants() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let base = VirtAddr::from((top.start - 1) * TOP_SIZE);
                let frame = PhysAddr::from(arena.base());
                let kernel_leaf = kernel.walk(VirtAddr::from(arena.base())).read().raw();
                user.map(common::page_2m(base), common::frame_2m(frame), common::flags(), false)
                    .unwrap();
                discharge(split_at!(user, base, SMALL_LEVEL, true).unwrap());
                assert_eq!(user.walk(base).level(), SMALL_LEVEL);
                discharge(set_flags_at!(user, base, SMALL_LEVEL, readonly(), true).unwrap());
                assert_readonly(user.walk(base).read());
                assert_eq!(user.phys_addr(base), Ok(frame));
                discharge(user.set_shared(common::page_4k(base), true).unwrap());
                discharge(user.set_private(common::page_4k(base), true).unwrap());
                let (old, pending) = user.unmap(common::page_4k(base), true).unwrap();
                let old = old.unwrap();
                assert_eq!(old.leaf_address(SMALL_LEVEL), frame);
                assert_readonly(old);
                discharge(pending);
                assert_eq!(user.phys_addr(base), Err(PagingError::NotMapped));
                assert_eq!(user.phys_addr(base + PAGE), Ok(frame + PAGE));

                let addr = base + 2 * LARGE;
                user.map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false)
                    .unwrap();
                let (old, pending) = user.unmap(common::page_4k(addr), true).unwrap();
                assert!(old.is_some());
                discharge(pending);
                let addr = base + 4 * LARGE;
                user.map_with_parent_flags(
                    common::page_4k(addr),
                    common::frame_4k(frame),
                    common::flags(),
                    false,
                    PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER,
                )
                .unwrap();
                let (old, pending) = unmap_at!(user, addr, SMALL_LEVEL).unwrap();
                assert!(old.is_some());
                discharge(pending);
                let addr = base + 6 * LARGE;
                map_at!(user, addr, frame, LARGE_LEVEL, common::flags(), false).unwrap();
                let (old, pending) = user.unmap(common::page_2m(addr), true).unwrap();
                assert!(old.is_some());
                discharge(pending);

                let start = base + 8 * LARGE;
                let end = start + 2 * PAGE;
                for offset in (0..end - start).step_by(PAGE) {
                    user.map(
                        common::page_4k(start + offset),
                        common::frame_4k(frame + offset),
                        common::flags(),
                        false,
                    )
                    .unwrap();
                }
                let (result, pending) = user.set_flags_range(start, end, readonly(), true);
                assert_eq!(result, Ok(()));
                discharge(pending);
                for addr in [start, start + PAGE] {
                    assert_readonly(user.walk(addr).read());
                }
                let (_, pending) = user.unmap_region(start, end).unwrap();
                discharge(pending);
                let large_start = start + 2 * LARGE;
                user.map(
                    common::page_2m(large_start),
                    common::frame_2m(frame),
                    common::flags(),
                    false,
                )
                .unwrap();
                user.map(
                    common::page_2m(large_start + LARGE),
                    common::frame_2m(frame + LARGE),
                    common::flags(),
                    false,
                )
                .unwrap();
                let (_, pending) = user.unmap_region(large_start, large_start + 2 * LARGE).unwrap();
                discharge(pending);
                map_region_4k!(user, start, end, frame, common::flags()).unwrap();
                let (mapped, pending) = user.unmap_region(start, end).unwrap();
                assert!(mapped);
                discharge(pending);
                map_region_4k!(user, start, end, frame, common::flags()).unwrap();
                assert_eq!(user.phys_addr(start + PAGE), Ok(frame + PAGE));
                assert_eq!(kernel.phys_addr(start), Err(PagingError::NotMapped));
                assert_eq!(kernel.walk(VirtAddr::from(arena.base())).read().raw(), kernel_leaf);
                assert_eq!(user.validate_page_table(), Ok(()));
                // SAFETY: only private descendants are reclaimed while the kernel is borrowed.
                unsafe { user.free_children() };
                drop(user);
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn unmapping_from_inside_a_huge_leaf_preserves_its_uncovered_prefix() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let base = VirtAddr::from((top.start - 1) * TOP_SIZE);
                let neighbor = base + LARGE;
                let end = neighbor + PAGE;
                let frame = PhysAddr::from(arena.base());
                user.map(common::page_2m(base), common::frame_2m(frame), common::flags(), false)
                    .unwrap();
                user.map(
                    common::page_4k(neighbor),
                    common::frame_4k(frame + PAGE),
                    common::flags(),
                    false,
                )
                .unwrap();
                user.map(
                    common::page_4k(end),
                    common::frame_4k(frame + 2 * PAGE),
                    common::flags(),
                    false,
                )
                .unwrap();
                let (mapped, pending) = user.unmap_region(base + PAGE, end).unwrap();
                assert!(mapped);
                discharge(pending);
                assert_eq!(user.phys_addr(base), Ok(frame));
                for addr in [base + PAGE, neighbor] {
                    assert_eq!(user.phys_addr(addr), Err(PagingError::NotMapped));
                }
                assert_eq!(user.phys_addr(end), Ok(frame + 2 * PAGE));
                assert_eq!(user.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
                assert_eq!(kernel.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
                // SAFETY: private descendants are inactive; shared kernel pages remain borrowed.
                unsafe { user.free_children() };
                drop(user);
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn dropping_a_user_reclaims_private_tables_without_touching_shared_kernel_tables() {
                let (arena, mut kernel, locks) = $fixture();
                let shared_address = VirtAddr::from(reserved_hole(&arena) * TOP_SIZE);
                let frame = PhysAddr::from(0x1000usize);
                kernel
                    .map(
                        common::page_4k(shared_address),
                        common::frame_4k(frame),
                        common::flags(),
                        false,
                    )
                    .unwrap();
                let shared_word = kernel.walk(shared_address).read().raw();
                let kernel_pages = arena.allocated();
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let root = user.root_paddr();
                for address in [VirtAddr::from(0usize), VirtAddr::from(0xffff_ff80_0000_0000usize)]
                {
                    user.map(
                        common::page_4k(address),
                        common::frame_4k(frame),
                        common::flags(),
                        false,
                    )
                    .unwrap();
                    assert_eq!(user.phys_addr(address), Ok(frame));
                }
                let private_pages: BTreeSet<_> = (kernel_pages..arena.allocated())
                    .map(|index| arena.base() + index * PAGE)
                    .collect();
                assert_eq!(private_pages.len(), 7);
                assert_eq!(user.walk(shared_address).read().raw(), shared_word);
                assert!(arena.freed().is_empty());
                drop(user);
                let freed = arena.freed();
                assert_eq!(freed.len(), private_pages.len());
                assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>(), private_pages);
                assert_eq!(freed.last(), Some(&root.bits()));
                assert_eq!(kernel.walk(shared_address).read().raw(), shared_word);
                assert_eq!(kernel.phys_addr(shared_address), Ok(frame));
                assert_eq!(kernel.validate_page_table(), Ok(()));
                assert_eq!(Arc::strong_count(&arena), 1);
                drop(kernel);
                assert_reclaimed(&arena);
                assert_eq!(Arc::strong_count(&arena), 1);
            }

            #[test]
            fn child_cleanup_preserves_shared_pointers_and_reclaims_only_owned_descendants() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let shared_index = direct_map_index(&arena);
                let kernel_pages = arena.allocated();
                let kernel_addr = VirtAddr::from(arena.base());
                let shared_pointer = kernel.next_table_pa(shared_index);
                assert!(shared_pointer.is_some());
                let shared_leaf = kernel.walk(kernel_addr).read().raw();
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let user_root = user.root_paddr();
                let private = VirtAddr::from((top.start - 1) * TOP_SIZE);
                user.map(
                    common::page_4k(private),
                    common::frame_4k(PhysAddr::from(arena.base())),
                    common::flags(),
                    false,
                )
                .unwrap();
                let owned_children = arena.allocated() - kernel_pages - 1;
                assert_eq!(owned_children, 3);
                // SAFETY: no hardware walks these roots; kernel pages must be skipped.
                assert_eq!(unsafe { user.free_page_table_by_addr(kernel_addr) }, 0);
                assert!(arena.freed().is_empty());
                unsafe { user.free_children() };
                assert_eq!(arena.freed().len(), owned_children);
                assert!(arena.freed().iter().all(|page| *page > user_root.bits()));
                assert_eq!(user.next_table_pa(shared_index), shared_pointer);
                assert_eq!(user.walk(kernel_addr).read().raw(), shared_leaf);
                assert_eq!(user.phys_addr(private), Err(PagingError::NotMapped));
                assert_eq!(user.validate_page_table(), Ok(()));
                unsafe { user.free_children() };
                assert_eq!(arena.freed().len(), owned_children);
                drop(user);
                assert_eq!(arena.freed().len(), owned_children + 1);
                assert!(arena.freed().contains(&user_root.bits()));
                assert_eq!(kernel.next_table_pa(shared_index), shared_pointer);
                assert_eq!(kernel.walk(kernel_addr).read().raw(), shared_leaf);
                discharge(
                    set_flags_at!(kernel, kernel_addr, LARGE_LEVEL, readonly(), true).unwrap(),
                );
                // SAFETY: the user is gone; all remaining pages belong to the inactive kernel.
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn range_cleanup_skips_even_empty_kernel_paths_when_spanning_both_domains() {
                let (arena, mut kernel, locks) = $fixture();
                let top = kernel_top(&arena);
                let boundary = VirtAddr::from(top.start * TOP_SIZE);
                let private = boundary - PAGE;
                let frame = PhysAddr::from(arena.base());
                assert_eq!(kernel.phys_addr(boundary), Err(PagingError::NotMapped));
                kernel
                    .map(common::page_4k(boundary), common::frame_4k(frame), common::flags(), false)
                    .unwrap();
                discharge(kernel.unmap(common::page_4k(boundary), true).unwrap().1);
                let kernel_pages = arena.allocated();
                let pointer = kernel.next_table_pa(top.start);
                let mut user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                let root = user.root_paddr();
                user.map(common::page_4k(private), common::frame_4k(frame), common::flags(), false)
                    .unwrap();
                discharge(user.unmap(common::page_4k(private), true).unwrap().1);
                let private_pages = arena.allocated() - kernel_pages - 1;
                // SAFETY: leaf flushes are discharged; shared kernel paths must remain linked.
                assert_eq!(unsafe { user.free_page_table_by_addr(boundary) }, 0);
                assert!(arena.freed().is_empty());
                unsafe { user.free_page_table_by_range(private, boundary + PAGE) };
                assert_eq!(arena.freed().len(), private_pages);
                assert!(arena.freed().iter().all(|page| *page > root.bits()));
                assert_eq!(user.next_table_pa(top.start - 1), None);
                assert_eq!(user.next_table_pa(top.start), pointer);
                assert_eq!(user.walk(boundary).level(), SMALL_LEVEL);
                assert_eq!(kernel.walk(boundary).level(), SMALL_LEVEL);
                assert_eq!(user.phys_addr(VirtAddr::from(arena.base())), Ok(frame));
                assert_eq!(user.validate_page_table(), Ok(()));
                drop(user);
                // SAFETY: the shared root was dropped, so the kernel may reclaim its empty path.
                assert!(unsafe { kernel.free_page_table_by_addr(boundary) } > 0);
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }

            #[test]
            fn leaking_a_user_returns_its_borrow_and_ownership_token_without_freeing_pages() {
                let (arena, mut kernel, locks) = $fixture();
                {
                    let top = kernel_top(&arena);
                    let user = $share::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
                    let root = user.root_paddr();
                    let (policy, leaked_root) = $leak(user);
                    assert_eq!(leaked_root, root);
                    assert!(top.clone().all(|index| policy.borrows_top_entry(index)));
                    assert!(!policy.owns_top_entry(direct_map_index(&arena)));
                    let empty = reserved_hole(&arena);
                    assert_eq!(kernel.next_table_pa(empty), None);
                    assert!(!policy.owns_top_entry(empty));
                    assert!(policy.owns_top_entry(top.start - 1));
                    assert!(policy.owns_top_entry(top.end));
                    assert!(arena.freed().is_empty());
                    assert_eq!(
                        kernel.phys_addr(VirtAddr::from(arena.base())),
                        Ok(PhysAddr::from(arena.base()))
                    );
                    // SAFETY: this inactive root has no owned descendants and no remaining users.
                    unsafe { Allocator::deallocate_table_page(root) };
                }
                unsafe { kernel.free_children() };
                drop(kernel);
                assert_reclaimed(&arena);
            }
        }
    };
}

policy_tests!(selected_controller, fixture, user, leak);

#[test]
fn const_generic_user_policies_and_controllers_have_no_storage_overhead() {
    assert_eq!(size_of::<Table>(), size_of::<(Allocator, PhysAddr, WholeTreeLock)>());
    assert_eq!(
        size_of::<KernelPageTable<Arch, Allocator, Lvl<4>, WholeTreeLock>>(),
        size_of::<(Allocator, PhysAddr, WholeTreeLock)>()
    );
    assert_eq!(size_of::<UserPolicy<'static, Reserved<KERNEL_START, KERNEL_END>>>(), 0);
    assert_eq!(size_of::<UserPolicy<'static, Reserved<2, 510>>>(), 0);
    assert_eq!(size_of::<UserPolicy<'static, Reserved<0, 512>>>(), 0);
    assert_eq!(size_of::<User<'static, KERNEL_START, KERNEL_END>>(), size_of::<Table>());
    assert_eq!(size_of::<User<'static, 2, 510>>(), size_of::<Table>());
    assert_eq!(
        size_of::<
            UserPageTable<
                'static,
                Arch,
                Allocator,
                Lvl<3>,
                WholeTreeLock<u64>,
                Reserved<2, 510>,
                u64,
            >,
        >(),
        size_of::<KernelPageTable<Arch, Allocator, Lvl<3>, WholeTreeLock<u64>, u64>>(),
    );
}

#[test]
fn concurrent_user_leak_returns_policy_and_content_domain() {
    type MetadataKernel = KernelPageTable<Arch, Allocator, Lvl<3>, WholeTreeLock<u64>, u64>;
    let arena = Arena::new(ARENA);
    let locks = WholeTreeLock::<u64>::default();
    *locks.lock(PhysAddr::from(0usize)) = 73;
    let kernel = MetadataKernel::new(locks.clone(), common::flags()).unwrap();
    let user =
        unsafe { MetadataKernel::new_from_sharing_top::<Reserved<0, 512>>(locks.clone(), &kernel) }
            .unwrap();
    let expected_root = user.root_paddr();
    let (content, policy, root) = user.leak();
    assert_eq!(root, expected_root);
    assert_eq!(Arc::strong_count(&arena), 1);
    assert!((0..512).all(|index| policy.borrows_top_entry(index)));
    assert!(!(0..512).any(|index| policy.owns_top_entry(index)));
    let acquired = locks.acquisitions();
    {
        let mut guard = content.lock(PhysAddr::from(0usize));
        assert_eq!(*guard, 73);
        *guard = 89;
    }
    assert_eq!(locks.acquisitions(), acquired + 1);
    assert_eq!(*locks.lock(PhysAddr::from(0usize)), 89);
    assert!(arena.freed().is_empty());
    // SAFETY: this leaked, inactive root owns no descendants; the kernel retains all shared pages.
    unsafe { Allocator::deallocate_table_page(root) };
    drop((policy, content));
    assert_eq!(kernel.validate_page_table(), Ok(()));
    drop(kernel);
    assert_reclaimed(&arena);
    assert_eq!(Arc::strong_count(&arena), 1);
}

#[test]
fn concurrent_kernel_updates_are_visible_with_independent_user_locks() {
    let (arena, mut kernel, locks) = fixture();
    let shared_index = direct_map_index(&arena);
    assert_direct_map_in::<KERNEL_START, KERNEL_END>(&arena);
    let user = unsafe {
        Table::new_from_sharing_top::<Reserved<KERNEL_START, KERNEL_END>>(
            WholeTreeLock::default(),
            &kernel,
        )
    }
    .unwrap();
    let addr = VirtAddr::from(shared_index * TOP_SIZE);
    let frame = PhysAddr::from(arena.base());
    let pointer = user.next_table_pa(shared_index);
    assert!(pointer.is_some());
    assert_eq!(user.phys_addr(addr), Err(PagingError::NotMapped));
    std::thread::scope(|scope| {
        scope
            .spawn(|| {
                kernel
                    .map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false)
                    .unwrap()
            })
            .join()
            .unwrap();
        assert_eq!(user.phys_addr(addr), Ok(frame));
        let acquired = locks.acquisitions();
        assert_error(
            set_flags_at!(user, addr, SMALL_LEVEL, readonly(), true),
            PagingError::PermissionDenied,
        );
        assert_eq!(locks.acquisitions(), acquired);
        assert!(user.walk(addr).read().writable());
        scope
            .spawn(|| {
                discharge(set_flags_at!(kernel, addr, SMALL_LEVEL, readonly(), true).unwrap())
            })
            .join()
            .unwrap();
        assert_readonly(user.walk(addr).read());
        scope
            .spawn(|| discharge(kernel.unmap(common::page_4k(addr), true).unwrap().1))
            .join()
            .unwrap();
        assert_eq!(user.phys_addr(addr), Err(PagingError::NotMapped));
        let acquired = locks.acquisitions();
        assert_error(
            set_flags_at!(user, addr, SMALL_LEVEL, common::flags(), true),
            PagingError::PermissionDenied,
        );
        assert_eq!(locks.acquisitions(), acquired);
        scope
            .spawn(|| {
                kernel
                    .map(common::page_4k(addr), common::frame_4k(frame + PAGE), readonly(), false)
                    .unwrap()
            })
            .join()
            .unwrap();
        assert_eq!(user.phys_addr(addr), Ok(frame + PAGE));
        assert_error(user.unmap(common::page_4k(addr), true), PagingError::PermissionDenied);
        scope
            .spawn(|| discharge(kernel.unmap(common::page_4k(addr), true).unwrap().1))
            .join()
            .unwrap();
        assert_eq!(user.phys_addr(addr), Err(PagingError::NotMapped));
    });
    assert_eq!(user.next_table_pa(shared_index), pointer);
    assert_eq!(user.validate_page_table(), Ok(()));
    drop(user);
    // SAFETY: all writers joined and the borrowed root is gone.
    unsafe { kernel.free_children() };
    drop(kernel);
    assert_reclaimed(&arena);
}

#[test]
fn later_kernel_root_growth_leaves_a_reserved_user_hole_protected() {
    let (arena, mut kernel, locks) = fixture();
    let mut user = user::<KERNEL_START, KERNEL_END>(&arena, &kernel, &locks);
    let empty = reserved_hole(&arena);
    let addr = VirtAddr::from(empty * TOP_SIZE);
    let frame = PhysAddr::from(arena.base());
    assert_eq!(kernel.next_table_pa(empty), None);
    kernel.map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false).unwrap();
    assert_eq!(kernel.phys_addr(addr), Ok(frame));
    assert_eq!(user.next_table_pa(empty), None);
    assert_eq!(user.phys_addr(addr), Err(PagingError::NotMapped));
    let allocated = arena.allocated();
    let acquired = locks.acquisitions();
    assert_error(
        user.map(common::page_4k(addr), common::frame_4k(frame), common::flags(), false),
        PagingError::PermissionDenied,
    );
    assert_error(user.unmap(common::page_4k(addr), true), PagingError::PermissionDenied);
    assert_eq!(arena.allocated(), allocated);
    assert_eq!(locks.acquisitions(), acquired);
    // SAFETY: cleanup must leave both copied and later-created kernel pages untouched.
    unsafe { user.free_children() };
    assert!(arena.freed().is_empty());
    assert_eq!(kernel.phys_addr(addr), Ok(frame));
    drop(user);
    unsafe { kernel.free_children() };
    drop(kernel);
    assert_reclaimed(&arena);
}
