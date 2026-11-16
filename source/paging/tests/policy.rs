//! Ensures ownership boundaries block unauthorized updates and prevent premature shared-subtree reclamation.
mod common;

use std::sync::atomic::Ordering;

use common::{Allocator, Host, Table};
use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{PTEntryFlags, X86_64Paging},
    structs::{
        CoveredRange, DirectMappedAllocator, Lvl, MayFreePageTablePages, NoRootEntries,
        OwnedSubtree, PageLevel, PagingError, PagingOwnershipPolicy, Policy, RootComplement,
        RootUnion, UserPolicy, PT_ENTRY_COUNT,
    },
};

const PAGE: usize = 4096;

#[test]
fn exclusive_canonical_boundary_does_not_include_the_kernel_half() {
    fn check<const START: usize, const END: usize>(root: PageLevel) {
        let low = VirtAddr::from((1usize << 47) - PAGE);
        let high = VirtAddr::from(1usize << 47);
        let policy = UserPolicy::<RootComplement<CoveredRange<START, END>>>::default();
        assert_eq!(policy.check_range(root, low, high), Ok(()));
        assert_eq!(policy.check_range(root, high, high), Ok(()));
        assert_eq!(policy.check_address(root, high), Err(PagingError::PermissionDenied));
        assert_eq!(policy.check_range(root, low, high + PAGE), Err(PagingError::PermissionDenied));
    }
    check::<256, 512>(PageLevel::Level3);
    check::<511, 512>(PageLevel::Level4);
}

#[test]
fn ranges_cannot_hide_protected_indexes_by_wrapping_a_small_root() {
    let root = PageLevel::Level0;
    let size = root.size();
    let span = PT_ENTRY_COUNT * size;
    let policy = UserPolicy::<RootComplement<CoveredRange<1, 2>>>::default();
    assert_eq!(
        policy.check_range(root, VirtAddr::from(0usize), VirtAddr::from(span)),
        Err(PagingError::PermissionDenied)
    );
    assert_eq!(
        policy.check_range(root, VirtAddr::from(span - size), VirtAddr::from(span + size)),
        Ok(())
    );
    assert_eq!(
        policy.check_range(root, VirtAddr::from(span - size), VirtAddr::from(span + 2 * size)),
        Err(PagingError::PermissionDenied)
    );
}

#[test]
fn adjacent_policy_ranges_cover_their_shared_boundary() {
    type Adjacent = RootUnion<CoveredRange<0, 2>, CoveredRange<2, 4>>;
    let root = PageLevel::Level3;
    let start = VirtAddr::from(root.size());
    let end = VirtAddr::from(3 * root.size());
    assert_eq!(UserPolicy::<Adjacent>::default().check_range(root, start, end), Ok(()));
    assert_eq!(
        UserPolicy::<RootComplement<Adjacent>>::default().check_range(root, start, end),
        Err(PagingError::PermissionDenied)
    );
}

#[test]
fn source_updates_are_visible_but_borrowers_cannot_mutate() {
    let (arena, source) = common::table();
    let address = VirtAddr::from(0usize);
    let frame = PhysAddr::from(arena.base());
    source.map(common::page_4k(address), common::frame_4k(frame), common::flags(), false).unwrap();
    // SAFETY: the inactive source outlives the borrower and retains all shared tables.
    let borrower = unsafe {
        Table::new_from_sharing_top::<UserPolicy<NoRootEntries>, _, _, _>(&source, |source| source)
    }
    .unwrap();
    let readonly = PTEntryFlags::PRESENT | PTEntryFlags::NX;
    assert!(matches!(
        borrower.set_flags(common::page_4k(address), readonly, true),
        Err(PagingError::PermissionDenied)
    ));
    let flush = source.set_flags(common::page_4k(address), readonly, true).unwrap();
    // SAFETY: hardware never observes these host-backed tables.
    unsafe { flush.ignore() };
    assert!(!borrower.walk(address).read().writable());
    assert_eq!(borrower.phys_addr(address), Ok(frame));
    drop(borrower);
    drop(source);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn rejected_sharing_does_not_free_or_retain_borrows_from_the_source() {
    let (arena, source) = common::table();
    let address = VirtAddr::from(0usize);
    let frame = PhysAddr::from(arena.base());
    source.map(common::page_4k(address), common::frame_4k(frame), common::flags(), false).unwrap();
    let child = source.next_table_pa(0).unwrap();
    // SAFETY: the inactive source stays live; the derived root cannot map its own tables.
    let result = unsafe {
        Table::new_from_sharing_top::<UserPolicy<CoveredRange<1, 512>>, _, _, _>(
            &source,
            |source| source,
        )
    };
    assert!(matches!(result, Err(PagingError::TablePageNotSelfMapped)));
    assert_eq!(Allocator::share_count(child).load(Ordering::Acquire), 0);
    assert_eq!(source.phys_addr(address), Ok(frame));
    assert_eq!(arena.freed().len(), 1);
    drop(source);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn source_reclamation_waits_for_the_last_borrower() {
    let (arena, mut source) = common::table();
    let index = (0..PT_ENTRY_COUNT).find(|index| source.next_table_pa(*index).is_none()).unwrap();
    let address = VirtAddr::from(index * PageLevel::Level3.size());
    source
        .map(
            common::page_4k(address),
            common::frame_4k(PhysAddr::from(arena.base())),
            common::flags(),
            false,
        )
        .unwrap();
    // SAFETY: the inactive source remains live until both borrowers are dropped.
    let first = unsafe {
        Table::new_from_sharing_top::<UserPolicy<NoRootEntries>, _, _, _>(&source, |source| source)
    }
    .unwrap();
    // SAFETY: as above, the source retains the shared tables.
    let second = unsafe {
        Table::new_from_sharing_top::<UserPolicy<NoRootEntries>, _, _, _>(&source, |source| source)
    }
    .unwrap();
    let child = source.next_table_pa(index).unwrap();
    let flush = source.unmap(common::page_4k(address), Some(true)).unwrap().1;
    // SAFETY: hardware never observes these host-backed tables.
    unsafe { flush.ignore() };
    assert_eq!(Allocator::share_count(child).load(Ordering::Acquire), 2);
    assert_eq!(common::reclaim_path(&mut source, address), 0);
    drop(first);
    assert_eq!(Allocator::share_count(child).load(Ordering::Acquire), 1);
    assert_eq!(common::reclaim_path(&mut source, address), 0);
    drop(second);
    assert_eq!(Allocator::share_count(child).load(Ordering::Acquire), 0);
    assert!(common::reclaim_path(&mut source, address) > 0);
    drop(source);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn nonfreeing_policy_retains_owned_children_on_drop() {
    type Retained = Policy<CoveredRange<0, 1>, true, { MayFreePageTablePages::Shared as u8 }>;
    let (arena, source) = common::table();
    // SAFETY: the source outlives the derived root and all tables remain inactive.
    let mut retained =
        unsafe { Table::new_from_sharing_top::<Retained, _, _, _>(&source, |source| source) }
            .unwrap();
    let address = VirtAddr::from(0usize);
    retained
        .map(
            common::page_4k(address),
            common::frame_4k(PhysAddr::from(arena.base())),
            common::flags(),
            false,
        )
        .unwrap();
    let child = retained.next_table_pa(0).unwrap();
    let flush = retained.unmap(common::page_4k(address), Some(true)).unwrap().1;
    // SAFETY: hardware never observes these host-backed tables.
    unsafe { flush.ignore() };
    assert_eq!(common::reclaim_path(&mut retained, address), 0);
    let root = retained.root_paddr();
    drop(retained);
    assert_eq!(arena.freed(), vec![root.bits()]);
    // SAFETY: the retaining root is gone; the private child has no remaining users.
    drop(unsafe { OwnedSubtree::<X86_64Paging<Host>, Allocator, Lvl<2>>::from_owned_root(child) });
    drop(source);
    assert_eq!(arena.freed().len(), arena.allocated());
}
