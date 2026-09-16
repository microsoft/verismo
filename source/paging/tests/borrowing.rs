//! External roots use ManuallyDrop; rejected controllers never own their roots.

mod common;

use std::mem::ManuallyDrop;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{Allocator, Arena, Host, ARENA};
use paging::address::{PhysAddr, VirtAddr};
#[cfg(feature = "use_ad")]
use paging::entry::PTEntry;
use paging::level::{Lvl, PageLevel};
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
#[cfg(feature = "use_ad")]
use paging::mapping::{MappingMut, MappingMutOps};
use paging::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use paging::pagetable::PageTable;
use paging::ptpage::PTPage;
use paging::{PTEntryFlags, X86Paging};

#[derive(Clone)]
struct BorrowAllocator {
    memory: Allocator,
    dropped: Arc<AtomicUsize>,
    panic_on_translate: bool,
}

// SAFETY: clones share the live host arena. Allocation is unsupported,
// so no frame can satisfy the deallocation precondition.
unsafe impl PagingAllocator for BorrowAllocator {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        assert!(!self.panic_on_translate, "injected translation panic");
        PagingAllocator::paddr_to_vaddr(&self.memory, paddr)
    }

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        PagingAllocator::vaddr_to_paddr(&self.memory, vaddr)
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        Err(PagingError::AllocFrame)
    }

    unsafe fn deallocate_table_page(&self, _paddr: PhysAddr) {
        panic!("foreign table page passed to borrower for deallocation");
    }
}

impl Drop for BorrowAllocator {
    fn drop(&mut self) {
        self.dropped.fetch_add(1, Ordering::SeqCst);
    }
}

#[cfg(feature = "concurrent")]
type Table = PageTable<X86Paging<Host>, BorrowAllocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type Table = PageTable<X86Paging<Host>, BorrowAllocator, Lvl<3>>;

unsafe fn borrow(
    allocator: BorrowAllocator,
    root: PhysAddr,
) -> Result<ManuallyDrop<Table>, PagingError> {
    #[cfg(feature = "concurrent")]
    return unsafe { Table::from_root(allocator, WholeTreeLock::default(), root) }
        .map(ManuallyDrop::new);
    #[cfg(not(feature = "concurrent"))]
    unsafe {
        Table::from_root(allocator, root).map(ManuallyDrop::new)
    }
}

macro_rules! borrowed_tests {
    ($module:ident, $borrow:path) => {
        mod $module {
            use super::*;

            #[test]
            fn borrowed_edits_leave_root_ownership_with_the_original_allocator() {
                let (arena, mut owner) = common::table();
                let addr = VirtAddr::from(0x4000_0000usize);
                owner.map_4k(addr, PhysAddr::from(arena.base()), common::flags(), false).unwrap();
                let root = owner.root_paddr();
                let original = owner.walk(addr).read().raw();
                let dropped = Arc::new(AtomicUsize::new(0));
                let allocator = BorrowAllocator {
                    memory: Allocator(arena.clone()),
                    dropped: dropped.clone(),
                    panic_on_translate: false,
                };
                // SAFETY: the owner stays alive and unused; the controller's Drop is suppressed.
                #[allow(unused_mut)]
                let mut view = unsafe { $borrow(allocator, root) }.unwrap();
                let readonly = PTEntryFlags::PRESENT | PTEntryFlags::NX;
                let pending = view.mprotect(addr, PageLevel::Level0, readonly, true).unwrap();
                // SAFETY: these host-backed tables are never installed.
                unsafe { pending.ignore() };
                assert_eq!(view.phys_addr(addr), Ok(PhysAddr::from(arena.base())));
                let protected = original & !(PTEntryFlags::WRITABLE | PTEntryFlags::GLOBAL).bits();
                assert_eq!(view.walk(addr).read().raw(), protected);
                assert_eq!(view.root_paddr(), root);
                assert_eq!(Arc::strong_count(&dropped), 2);
                let before_drop = dropped.load(Ordering::SeqCst);
                let _ = ManuallyDrop::into_inner(view).leak();
                assert_eq!(dropped.load(Ordering::SeqCst), before_drop + 1);
                assert_eq!(Arc::strong_count(&dropped), 1);
                assert!(arena.freed().is_empty());
                assert_eq!(owner.phys_addr(addr), Ok(PhysAddr::from(arena.base())));
                assert_eq!(owner.walk(addr).read().raw(), protected);
                assert_eq!(owner.validate_page_table(), Ok(()));
                // SAFETY: the borrower is gone; every page belongs to this inactive owner.
                unsafe { owner.free_children() };
                drop(owner);
                assert_eq!(arena.freed().len(), arena.allocated());
            }

            #[test]
            fn rejection_releases_the_allocator_without_freeing_the_borrowed_root() {
                let arena = Arena::new(ARENA);
                let owner = Allocator(arena.clone());
                let (_, root) = PTPage::<X86Paging<Host>, _>::alloc(&owner).unwrap();
                let dropped = Arc::new(AtomicUsize::new(0));
                let allocator = BorrowAllocator {
                    memory: Allocator(arena.clone()),
                    dropped: dropped.clone(),
                    panic_on_translate: false,
                };
                // SAFETY: this is a live, empty root; missing self-mapping is fallible.
                let result = unsafe { $borrow(allocator, root) };
                assert!(matches!(result, Err(PagingError::TablePageNotSelfMapped)));
                assert!(arena.freed().is_empty());
                assert_eq!(dropped.load(Ordering::SeqCst), 1);
                // SAFETY: the refused root is unlinked and still belongs to its allocator.
                unsafe { DirectMappedAllocator::deallocate_table_page(&owner, root) };
            }

            #[test]
            fn validation_unwinding_does_not_free_the_borrowed_root_or_leak_its_allocator() {
                let (arena, mut owner) = common::table();
                let root = owner.root_paddr();
                let dropped = Arc::new(AtomicUsize::new(0));
                let allocator = BorrowAllocator {
                    memory: Allocator(arena.clone()),
                    dropped: dropped.clone(),
                    panic_on_translate: true,
                };
                let result = catch_unwind(AssertUnwindSafe(|| {
                    // SAFETY: the owner remains alive and unused while validation runs.
                    unsafe { $borrow(allocator, root) }
                }));
                assert!(result.is_err());
                assert!(arena.freed().is_empty());
                assert_eq!(dropped.load(Ordering::SeqCst), 1);
                assert_eq!(owner.validate_page_table(), Ok(()));
                // SAFETY: validation unwound; the original owner is the sole controller.
                unsafe { owner.free_children() };
                drop(owner);
                assert_eq!(arena.freed().len(), arena.allocated());
            }
        }
    };
}

borrowed_tests!(selected_controller, borrow);

#[cfg(feature = "use_ad")]
#[test]
fn staged_commit_preserves_late_accessed_dirty_bits() {
    type Arch = X86Paging<Host>;

    let initial = PTEntry::<Arch>::new(
        PhysAddr::from(0x4000usize),
        PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE,
    );
    let word = AtomicUsize::new(initial.raw());
    let entry = (&word as *const AtomicUsize).cast_mut().cast::<PTEntry<Arch>>();
    // SAFETY: `word` has the entry's transparent layout and is accessed atomically.
    let mut mapping =
        unsafe { MappingMut::new(Some(VirtAddr::from(0x8000usize)), PageLevel::Level0, entry) };
    mapping
        .staged()
        .entry
        .set(PhysAddr::from(0x4000usize), PTEntryFlags::PRESENT | PTEntryFlags::NX);

    let hardware_ad = (PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY).bits();
    word.fetch_or(hardware_ad, Ordering::AcqRel);
    let pending = mapping.commit();
    // SAFETY: this host-only entry is never installed in a hardware page table.
    unsafe { pending.ignore() };

    let committed = PTEntryFlags::from_bits_retain(word.load(Ordering::Acquire));
    assert!(committed.contains(PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
    assert!(committed.contains(PTEntryFlags::PRESENT | PTEntryFlags::NX));
    assert!(!committed.contains(PTEntryFlags::WRITABLE));
}

#[cfg(feature = "use_ad")]
#[test]
#[should_panic(expected = "present leaf/table transitions require architecture-aware publication")]
fn staged_commit_rejects_present_leaf_table_transition() {
    type Arch = X86Paging<Host>;

    let initial = PTEntry::<Arch>::new(
        PhysAddr::from(0x20_0000usize),
        PTEntryFlags::PRESENT | PTEntryFlags::HUGE,
    );
    let word = AtomicUsize::new(initial.raw());
    let entry = (&word as *const AtomicUsize).cast_mut().cast::<PTEntry<Arch>>();
    // SAFETY: `word` has the entry's transparent layout and is accessed atomically.
    let mut mapping =
        unsafe { MappingMut::new(Some(VirtAddr::from(0x20_0000usize)), PageLevel::Level1, entry) };
    *mapping.staged().entry =
        PTEntry::new_table(PhysAddr::from(0x40_0000usize), PTEntryFlags::PRESENT);
    let _ = mapping.commit();
}
