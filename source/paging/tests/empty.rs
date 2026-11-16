//! Ensures empty roots need no initial self-map while still enforcing ownership and allocation cleanup.
mod common;
use std::prelude::rust_2021::*;

use std::sync::atomic::{AtomicUsize, Ordering};

use common::{Allocator, Arena, Host, ARENA};
use paging::{
    address::{PhysAddr, VirtAddr},
    arch::x86_64::X86_64Paging,
    pagetable::{KernelPageTable, UserPageTable},
    structs::{CoveredRange, Lvl, PagingAllocator, PagingError},
};

struct Provider;

// SAFETY: all allocation and access obligations are delegated to the arena provider.
unsafe impl PagingAllocator for Provider {
    fn paddr_to_vaddr(address: PhysAddr) -> VirtAddr {
        Allocator::paddr_to_vaddr(address)
    }

    fn vaddr_to_paddr(address: VirtAddr) -> PhysAddr {
        Allocator::vaddr_to_paddr(address)
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        Allocator::allocate_table_page()
    }

    unsafe fn deallocate_table_page(address: PhysAddr) {
        // SAFETY: the caller transfers an arena allocation with no remaining users.
        unsafe { Allocator::deallocate_table_page(address) };
    }

    fn share_count(address: PhysAddr) -> &'static AtomicUsize {
        Allocator::share_count(address)
    }
}

type Arch = X86_64Paging<Host>;
type Kernel = KernelPageTable<Arch, Provider, Lvl<3>>;
type User = UserPageTable<Arch, Provider, Lvl<3>, CoveredRange<0, 1>>;
const TOP_SIZE: usize = 1 << 39;

#[test]
fn empty_root_uses_only_paging_allocator_and_reclaims_private_tables() {
    let arena = Arena::new(ARENA);

    let table = Kernel::new_empty().unwrap();
    assert_eq!(arena.allocated(), 1);
    assert!((0..512).all(|index| table.next_table_pa(index).is_none()));
    assert_eq!(table.phys_addr(0x400000usize.into()), Err(PagingError::NotMapped));
    let frame = PhysAddr::from(0x10000000usize);
    table
        .map(common::page_4k(0x400000usize.into()), common::frame_4k(frame), common::flags(), false)
        .unwrap();
    assert_eq!(table.phys_addr(0x400000usize.into()), Ok(frame));
    let (_, pending) = table.unmap(common::page_4k(0x400000usize.into()), Some(true)).unwrap();
    // SAFETY: this test never activates the root in hardware.
    unsafe { pending.ignore() };
    assert_eq!(table.phys_addr(0x400000usize.into()), Err(PagingError::NotMapped));
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn exhausted_allocator_reports_failure_without_disturbing_an_existing_root() {
    let arena = Arena::new(4096);
    let table = Kernel::new_empty().unwrap();
    assert!(matches!(Kernel::new_empty(), Err(PagingError::AllocFrame)));
    assert_eq!(arena.allocated(), 1);
    assert!(arena.freed().is_empty());
    assert!((0..512).all(|index| table.next_table_pa(index).is_none()));
    drop(table);
    assert_eq!(arena.freed().len(), 1);
}

#[test]
fn empty_user_root_preserves_ownership_checks_and_can_borrow_later() {
    let arena = Arena::new(ARENA);
    let kernel = Kernel::new_empty().unwrap();
    let mut user = User::new_empty().unwrap();
    let address = VirtAddr::from(TOP_SIZE);
    let frame = common::frame_4k(PhysAddr::from(0x10000000usize));
    assert_eq!(
        user.map(common::page_4k(address), frame, common::flags(), false),
        Err(PagingError::PermissionDenied),
    );
    assert_eq!(arena.allocated(), 2);
    kernel.map(common::page_4k(address), frame, common::flags(), false).unwrap();
    let child = kernel.next_table_pa(1).unwrap();
    // SAFETY: the inactive kernel outlives the borrower and retains its shared branch.
    unsafe { user.populate_shared(1, &kernel, |source| source) }.unwrap();
    assert_eq!(Provider::share_count(child).load(Ordering::Acquire), 1);
    assert_eq!(user.phys_addr(address), kernel.phys_addr(address));
    user.map(common::page_4k(0x400000usize.into()), frame, common::flags(), false).unwrap();
    drop(user);
    assert_eq!(Provider::share_count(child).load(Ordering::Acquire), 0);
    assert_eq!(kernel.phys_addr(address), Ok(frame.start_address()));
    drop(kernel);
    assert_eq!(arena.freed().len(), arena.allocated());
}
