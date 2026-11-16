//! Ensures CPU-local bindings retain roots across failed switches and until hardware users are excluded.
mod common;
use std::cell::Cell;
use std::mem::ManuallyDrop;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::prelude::rust_2021::*;
use std::sync::Arc;

use common::{Allocator, Arena, Host, ARENA};
use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{PTEntryFlags, X86TlbFlushTok, X86_64Paging},
    pagetable::{
        ActivationFailure, ActivePageTable, KernelPageTable, RootRegisterAccess, UserPageTable,
    },
    structs::{
        AllRootEntries, ArchPagingMeta, KernelPolicy, LevelSpec, Lvl, PageLevel, PagingError,
        PagingOwnershipPolicy,
    },
};

#[derive(Clone, Copy)]
struct Model;

impl ArchPagingMeta for Model {
    type PTFlags = PTEntryFlags;
    type TlbFlushTok = X86TlbFlushTok<Host>;

    fn private_pte_mask() -> usize {
        0
    }
    fn shared_pte_mask() -> usize {
        0
    }
    fn address_mask() -> usize {
        X86_64Paging::<Host>::address_mask()
    }
    fn accessed_dirty_mask() -> usize {
        X86_64Paging::<Host>::accessed_dirty_mask()
    }
    fn leaf_flags_mask() -> PTEntryFlags {
        X86_64Paging::<Host>::leaf_flags_mask()
    }
    fn requires_break_before_make<L: LevelSpec>(_: usize, _: usize) -> bool {
        false
    }
}

const SUCCEED: usize = 0;
const REJECT: usize = 1;
const PANIC_AFTER_WRITE: usize = 2;

std::thread_local! {
    static ROOT: Cell<usize> = const { Cell::new(0) };
}

// SAFETY: this model has no hardware consumers. Register state is CPU-local,
// rejection precedes writes, and success records exactly the supplied root.
unsafe impl RootRegisterAccess for Model {
    unsafe fn read_root_pa() -> PhysAddr {
        ROOT.with(Cell::get).into()
    }

    unsafe fn store_root_pa<L: LevelSpec>(root: PhysAddr, flags: usize) -> Result<(), PagingError> {
        assert_eq!(L::LEVEL, PageLevel::Level3);
        if flags == REJECT {
            return Err(PagingError::InvalidFlags);
        }
        ROOT.with(|current| current.set(root.bits()));
        if flags == PANIC_AFTER_WRITE {
            std::panic!("injected failure after changing the root");
        }
        Ok(())
    }
}

type Table = KernelPageTable<Model, Allocator, Lvl<3>>;
type ActiveTable = ActivePageTable<Model, Allocator, Lvl<3>, KernelPolicy>;

fn fixture() -> Arc<Arena> {
    let arena = Arena::new(ARENA);
    ROOT.with(|current| current.set(0));
    arena
}

fn table() -> Table {
    Table::new(common::flags()).unwrap()
}

fn adopt(table: Table) -> ActiveTable {
    let root = table.leak();
    ROOT.with(|current| current.set(root.bits()));
    // SAFETY: the leaked tree is transferred once to this CPU-local model binding.
    unsafe { ActiveTable::from_current_cpu() }.unwrap()
}

fn reclaim_retained(root: PhysAddr) {
    ROOT.with(|current| current.set(0));
    // SAFETY: the model has no hardware consumers; ownership of this retained
    // all-root kernel table is returned exactly once after switching it out.
    drop(unsafe { Table::from_root(root) }.unwrap());
}

fn reclaim_active<S: PagingOwnershipPolicy>(active: ActivePageTable<Model, Allocator, Lvl<3>, S>) {
    // SAFETY: switching the model does not affect real hardware consumers.
    let (parking, retired) = unsafe { active.switch_to(table(), SUCCEED) }.unwrap();
    ROOT.with(|current| current.set(0));
    // SAFETY: no real hardware consumes either model root.
    drop(unsafe { retired.into_page_table() });
    reclaim_retained(parking.leak());
}

#[test]
fn adopting_the_current_root_preserves_the_register_and_allocations() {
    let arena = fixture();
    let root = table().leak();
    ROOT.with(|current| current.set(root.bits()));
    let allocated = arena.allocated();
    // SAFETY: the leaked tree's ownership is transferred once; the model has no hardware users.
    let active = unsafe { ActiveTable::from_current_cpu() }.unwrap();
    assert_eq!(active.root_paddr(), root);
    assert_eq!(ROOT.with(Cell::get), root.bits());
    assert_eq!(arena.allocated(), allocated);
    assert!(arena.freed().is_empty());
    reclaim_active(active);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn rejecting_an_invalid_current_tree_retains_its_allocation() {
    let arena = fixture();
    let empty = ManuallyDrop::new(Table::new_empty().unwrap());
    let root = empty.root_paddr();
    ROOT.with(|current| current.set(root.bits()));
    // SAFETY: the model has no hardware users; the retained controller is unusable
    // unless adoption fails, and the tree remains accessible throughout validation.
    let error = match unsafe { ActiveTable::from_current_cpu() } {
        Err(error) => error,
        Ok(_) => std::panic!("an unmapped current root passed validation"),
    };
    assert_eq!(error, PagingError::TablePageNotSelfMapped);
    assert_eq!(ROOT.with(Cell::get), root.bits());
    assert!(arena.freed().is_empty());
    ROOT.with(|current| current.set(0));
    drop(ManuallyDrop::into_inner(empty));
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn active_bindings_allow_shared_updates_and_switch_without_reclaiming_the_old_tree() {
    let arena = fixture();
    let first = table();
    let first_root = first.root_paddr();
    let next = UserPageTable::<Model, Allocator, Lvl<3>, AllRootEntries>::new_empty().unwrap();
    let start = VirtAddr::from(arena.base());
    let range = common::range_4k(start, start + arena.len());
    let mut frames = common::contiguous_frames_4k(PhysAddr::from(arena.base()), range.len());
    next.map_region(range, &mut frames, common::flags()).unwrap();
    let second_root = next.root_paddr();
    let active = adopt(first);
    assert_eq!(active.root_paddr(), first_root);
    let address = 0x4000_0000usize.into();
    let frame = PhysAddr::from(0x1000_0000usize);
    active.map(common::page_4k(address), common::frame_4k(frame), common::flags(), false).unwrap();
    assert_eq!(active.phys_addr(address), Ok(frame));
    let before_switch = arena.freed().len();
    // SAFETY: both roots are accessible and register writes stay on this model CPU.
    let (active, retired) = unsafe { active.switch_to(next, SUCCEED) }.unwrap();
    assert_eq!(ROOT.with(Cell::get), second_root.bits());
    assert_eq!(retired.phys_addr(address), Ok(frame));
    assert_eq!(arena.freed().len(), before_switch);
    // SAFETY: no real hardware consumes either tree in this model.
    drop(unsafe { retired.into_page_table() });
    assert!(arena.freed().contains(&first_root.bits()));
    reclaim_active(active);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn rejected_and_stale_switches_preserve_both_resources() {
    let arena = fixture();
    let first = table();
    let first_root = first.root_paddr();
    let next = table();
    let next_root = next.root_paddr();
    let active = adopt(first);
    // SAFETY: rejection leaves the active model root unchanged.
    let error = match unsafe { active.switch_to(next, REJECT) } {
        Err(error) => error,
        Ok(_) => std::panic!("register rejection was ignored"),
    };
    assert_eq!(error.error, ActivationFailure::Paging(PagingError::InvalidFlags));
    let (active, next) = error.resources;
    assert_eq!(ROOT.with(Cell::get), first_root.bits());
    assert_eq!(active.root_paddr(), first_root);
    assert_eq!(next.root_paddr(), next_root);
    assert!(arena.freed().is_empty());
    // SAFETY: an unmapped model root must fail validation before register access.
    let error = match unsafe { active.switch_to(Table::new_empty().unwrap(), SUCCEED) } {
        Err(error) => error,
        Ok(_) => std::panic!("an unmapped root passed switch validation"),
    };
    assert_eq!(error.error, ActivationFailure::Paging(PagingError::TablePageNotSelfMapped));
    let (active, empty) = error.resources;
    assert_eq!(ROOT.with(Cell::get), first_root.bits());
    drop(empty);
    let freed = arena.freed().len();
    ROOT.with(|current| current.set(0));
    // SAFETY: this deliberately stale model binding must reject before loading next.
    let error = match unsafe { active.switch_to(next, SUCCEED) } {
        Err(error) => error,
        Ok(_) => std::panic!("a stale binding switched the root"),
    };
    assert_eq!(error.error, ActivationFailure::NotCurrent);
    let (active, next) = error.resources;
    assert_eq!(ROOT.with(Cell::get), 0);
    assert_eq!(arena.freed().len(), freed);
    drop(next);
    reclaim_retained(active.leak());
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn dropping_active_and_retired_handles_retains_allocations() {
    let arena = fixture();
    let first = table();
    let root = first.root_paddr();
    drop(adopt(first));
    assert_eq!(ROOT.with(Cell::get), root.bits());
    assert!(arena.freed().is_empty());
    reclaim_retained(root);
    let first = table();
    let root = first.root_paddr();
    let active = adopt(first);
    // SAFETY: both model roots are accessible.
    let (active, retired) = unsafe { active.switch_to(table(), SUCCEED) }.unwrap();
    let freed = arena.freed().len();
    drop(retired);
    assert_eq!(arena.freed().len(), freed);
    let active_root = active.leak();
    ROOT.with(|current| current.set(0));
    reclaim_retained(root);
    reclaim_retained(active_root);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn switch_hook_unwinding_retains_both_roots() {
    let arena = fixture();
    let first = table();
    let old_root = first.root_paddr();
    let next = table();
    let next_root = next.root_paddr();
    let active = adopt(first);
    let result = catch_unwind(AssertUnwindSafe(|| {
        // SAFETY: only the register model is modified; its hook then panics.
        let _ = unsafe { active.switch_to(next, PANIC_AFTER_WRITE) };
    }));
    assert!(result.is_err());
    assert_eq!(ROOT.with(Cell::get), next_root.bits());
    assert!(arena.freed().is_empty());
    reclaim_retained(old_root);
    reclaim_retained(next_root);
    assert_eq!(arena.freed().len(), arena.allocated());
}

#[test]
fn switching_one_model_cpu_keeps_the_other_cpu_root_and_retired_pages_live() {
    use std::sync::mpsc;
    use std::time::Duration;

    let arena = fixture();
    let first = table();
    let root = first.root_paddr();
    let index = paging::structs::entry_index(VirtAddr::from(arena.base()), PageLevel::Level3);
    let active = adopt(first);
    let (ready, received) = mpsc::channel();
    let (release, resumed) = mpsc::channel();
    let other_cpu = std::thread::spawn(move || {
        // SAFETY: this is a separate modeled CPU; the owner retains the root.
        unsafe { Model::store_root_pa::<Lvl<3>>(root, SUCCEED) }.unwrap();
        ready.send(()).unwrap();
        resumed.recv_timeout(Duration::from_secs(10)).expect("modeled CPU was not released");
        assert_eq!(ROOT.with(Cell::get), root.bits());
        let page = root.bits() as *const paging::structs::PTPage<Model, Allocator>;
        // SAFETY: the retained owner pins this page until this worker joins.
        assert!(unsafe { common::load_entry(paging::structs::PTPage::entry_ptr(page, index)) }
            .present());
        ROOT.with(|current| current.set(0));
    });
    received.recv_timeout(Duration::from_secs(10)).expect("modeled CPU did not install the root");
    // SAFETY: both roots are accessible; this only switches the caller's model CPU.
    let (active, retired) = unsafe { active.switch_to(table(), SUCCEED) }.unwrap();
    assert_ne!(ROOT.with(Cell::get), root.bits());
    drop(retired);
    assert!(arena.freed().is_empty());
    release.send(()).unwrap();
    other_cpu.join().unwrap();
    let active_root = active.leak();
    reclaim_retained(root);
    reclaim_retained(active_root);
    assert_eq!(arena.freed().len(), arena.allocated());
}
