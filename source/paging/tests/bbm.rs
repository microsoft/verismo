//! Ensures architectures requiring break-before-make invalidate old entries before publishing replacements.
mod common;

use std::cell::{Cell, RefCell};
use std::sync::Arc;

use common::{Allocator, Arena, ARENA};
use paging::{
    address::{PhysAddr, VirtAddr},
    arch::x86_64::{FlushScope, PTEntryFlags, X86TlbFlushTok, X86_64Paging, X86_64PagingParams},
    pagetable::KernelPageTable,
    structs::{ArchPagingMeta, LevelSpec, Lvl, PageLevel},
};

type FlushHook = Box<dyn FnMut()>;
thread_local! {
    static HOOK: RefCell<Option<FlushHook>> = const { RefCell::new(None) };
    static FLUSHES: Cell<usize> = const { Cell::new(0) };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Tagged;

// SAFETY: the test never installs hardware roots, and callbacks only observe pinned tables.
unsafe impl X86_64PagingParams for Tagged {
    fn private_mask() -> usize {
        1 << 51
    }
    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }
    fn flush_tlb_global_sync(_: FlushScope) {
        FLUSHES.with(|count| count.set(count.get() + 1));
        HOOK.with(|hook| {
            if let Some(hook) = hook.borrow_mut().as_mut() {
                hook();
            }
        });
    }
}

#[derive(Clone, Copy)]
struct Bbm;
impl ArchPagingMeta for Bbm {
    type PTFlags = PTEntryFlags;
    type TlbFlushTok = X86TlbFlushTok<Tagged>;
    fn private_pte_mask() -> usize {
        Tagged::private_mask()
    }
    fn shared_pte_mask() -> usize {
        0
    }
    fn address_mask() -> usize {
        X86_64Paging::<Tagged>::address_mask()
    }
    fn accessed_dirty_mask() -> usize {
        X86_64Paging::<Tagged>::accessed_dirty_mask()
    }
    fn leaf_flags_mask() -> PTEntryFlags {
        X86_64Paging::<Tagged>::leaf_flags_mask()
    }
    fn requires_break_before_make<L: LevelSpec>(_: usize, _: usize) -> bool {
        true
    }
}

#[test]
fn splits_and_retagging_invalidate_before_publishing_the_replacement() {
    type Table = KernelPageTable<Bbm, Allocator, Lvl<3>>;
    let arena = Arena::new(ARENA);
    let table = Arc::new(Table::new(common::flags()).unwrap());
    let address = VirtAddr::from(0x4000_0000usize);
    table
        .map(
            common::page_2m(address),
            common::frame_2m(PhysAddr::from(arena.base())),
            common::flags(),
            false,
        )
        .unwrap();
    FLUSHES.with(|count| count.set(0));
    let old = table.walk(address).read().raw();
    let weak = Arc::downgrade(&table);
    HOOK.with(|hook| {
        *hook.borrow_mut() = Some(Box::new(move || {
            let table = weak.upgrade().expect("the test retains its table during the flush");
            assert_eq!(table.walk(address).read().raw(), old & !PTEntryFlags::PRESENT.bits());
        }));
    });
    table.split(common::page_2m(address), true).unwrap().expect_no_flush();
    HOOK.with(|hook| hook.borrow_mut().take());
    assert_eq!(table.walk(address).level(), PageLevel::Level0);
    assert_eq!(FLUSHES.with(Cell::get), 1);

    let old = table.walk(address).read().raw();
    let weak = Arc::downgrade(&table);
    HOOK.with(|hook| {
        *hook.borrow_mut() = Some(Box::new(move || {
            let table = weak.upgrade().expect("the test retains its table during the flush");
            assert_eq!(table.walk(address).read().raw(), old & !PTEntryFlags::PRESENT.bits());
        }));
    });
    table.set_shared(common::page_4k(address), true).unwrap().expect_no_flush();
    HOOK.with(|hook| hook.borrow_mut().take());
    assert_eq!(table.walk(address).read().raw(), old & !(1 << 51));
    assert_eq!(FLUSHES.with(Cell::get), 2);
    drop(table);
    assert_eq!(arena.freed().len(), arena.allocated());
}
