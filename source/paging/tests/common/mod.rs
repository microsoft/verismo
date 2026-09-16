//! A page table over host memory, so the tests can walk a real tree.
//!
//! The arena is a leaked, 2 MiB-aligned buffer, and the allocator direct-maps it
//! identically: a physical address in it is a host address the walk can
//! dereference. Allocator providers are stateless, so one arena is active at a
//! time within each test binary.
//!
//! Run them on a target that can execute:
//! `cargo test -p paging --target x86_64-unknown-linux-gnu`.
#![allow(dead_code)]

use std::cell::Cell;
use std::collections::BTreeSet;
use std::ops::Range;
use std::sync::atomic::{AtomicUsize, Ordering};
#[cfg(feature = "concurrent")]
use std::sync::MutexGuard;
use std::sync::{Arc, Condvar, Mutex};

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::Lvl;
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::{KernelPageTable, PageTable};
#[cfg(feature = "concurrent")]
use paging::pagetable::{LockAllSpec, LockSpec};
use paging::policy::PagingOwnershipPolicy;
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

/// Unencrypted memory whose TLB needs no invalidating: the host's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Host;

thread_local! {
    static HOST_FLUSHES: Cell<usize> = const { Cell::new(0) };
}

pub fn host_flushes() -> usize {
    HOST_FLUSHES.with(Cell::get)
}

unsafe impl X86PagingParams for Host {
    fn private_mask() -> usize {
        0
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(_scope: FlushScope) {
        HOST_FLUSHES.with(|count| count.set(count.get() + 1));
    }
}

/// A bump allocator over one leaked buffer, which remembers what was freed.
pub struct Arena {
    base: usize,
    len: usize,
    rebased_physical: AtomicUsize,
    state: Mutex<ArenaState>,
}

static ACTIVE_ARENA: Mutex<Option<usize>> = Mutex::new(None);
static ACTIVE_ARENA_CHANGED: Condvar = Condvar::new();

struct ArenaState {
    next: usize,
    live: BTreeSet<usize>,
    freed: Vec<usize>,
}

impl Arena {
    pub fn new(len: usize) -> Arc<Self> {
        assert!(len.is_power_of_two());
        let buf = vec![0u8; len * 2].leak();
        let base = (buf.as_mut_ptr() as usize + len - 1) & !(len - 1);
        let arena = Arc::new(Self {
            base,
            len,
            rebased_physical: AtomicUsize::new(base),
            state: Mutex::new(ArenaState { next: base, live: BTreeSet::new(), freed: Vec::new() }),
        });
        let mut active = ACTIVE_ARENA.lock().unwrap();
        while active.is_some() {
            active = ACTIVE_ARENA_CHANGED.wait(active).unwrap();
        }
        *active = Some(Arc::as_ptr(&arena) as usize);
        arena
    }

    pub fn base(&self) -> usize {
        self.base
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn rebase(&self, physical: usize) {
        self.rebased_physical.store(physical, Ordering::Relaxed);
    }

    /// How many pages have been handed out.
    pub fn allocated(&self) -> usize {
        (self.state.lock().unwrap().next - self.base) / 4096
    }

    pub fn freed(&self) -> Vec<usize> {
        self.state.lock().unwrap().freed.clone()
    }

    pub fn clear_freed(&self) {
        self.state.lock().unwrap().freed.clear();
    }

    fn active<R>(f: impl FnOnce(&Self) -> R) -> R {
        let active = ACTIVE_ARENA.lock().unwrap();
        let address = active.expect("no active paging test arena");
        drop(active);
        // SAFETY: each fixture retains its arena until all allocator calls finish.
        f(unsafe { &*(address as *const Self) })
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        let mut active = ACTIVE_ARENA.lock().unwrap();
        assert_eq!(*active, Some(self as *const Self as usize));
        *active = None;
        ACTIVE_ARENA_CHANGED.notify_one();
    }
}

/// The arena as a direct map: identity, so a walk can follow it on the host.
#[derive(Clone, Copy)]
pub struct Allocator;

#[derive(Clone, Copy)]
pub struct RebasedAllocator;

#[derive(Default)]
pub struct WholeTreeLock<T = ()> {
    content: Arc<Mutex<T>>,
    acquisitions: Arc<AtomicUsize>,
}

impl<T> Clone for WholeTreeLock<T> {
    fn clone(&self) -> Self {
        Self { content: self.content.clone(), acquisitions: self.acquisitions.clone() }
    }
}

impl<T> WholeTreeLock<T> {
    pub fn acquisitions(&self) -> usize {
        self.acquisitions.load(Ordering::Relaxed)
    }
}

// SAFETY: all keys and clones use one mutex, with the standard borrowed RAII guard.
#[cfg(feature = "concurrent")]
unsafe impl<T> LockSpec<T> for WholeTreeLock<T> {
    type Guard<'a>
        = MutexGuard<'a, T>
    where
        Self: 'a,
        T: 'a;

    fn lock(&self, _page: PhysAddr) -> Self::Guard<'_> {
        self.acquisitions.fetch_add(1, Ordering::Relaxed);
        self.content.lock().unwrap()
    }
}

// SAFETY: whole-domain and per-page guards exclude each other through the same mutex.
#[cfg(feature = "concurrent")]
unsafe impl<T> LockAllSpec<T> for WholeTreeLock<T> {
    type AllGuard<'a>
        = MutexGuard<'a, T>
    where
        Self: 'a,
        T: 'a;

    fn lock_all(&self) -> Self::AllGuard<'_> {
        self.lock(PhysAddr::from(0usize))
    }
}

unsafe impl DirectMappedAllocator for Allocator {
    fn direct_map() -> (core::ops::Range<PhysAddr>, VirtAddr) {
        Arena::active(|arena| {
            (
                PhysAddr::from(arena.base)..PhysAddr::from(arena.base + arena.len),
                VirtAddr::from(arena.base),
            )
        })
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        Arena::active(|arena| {
            let mut state = arena.state.lock().unwrap();
            if state.next + 4096 > arena.base + arena.len {
                return Err(PagingError::AllocFrame);
            }
            let page = state.next;
            state.next += 4096;
            assert!(state.live.insert(page));
            // SAFETY: this private arena page is poisoned to expose missing initialization.
            unsafe { core::ptr::write_bytes(page as *mut u8, 0xff, 4096) };
            Ok(PhysAddr::from(page))
        })
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        Arena::active(|arena| {
            let page = paddr.bits();
            assert_eq!(page % 4096, 0, "table page is not page-aligned");
            assert!(
                (arena.base..arena.base + arena.len).contains(&page),
                "table page is outside the arena"
            );
            let mut state = arena.state.lock().unwrap();
            assert!(page < state.next, "table page was not allocated by this arena");
            assert!(state.live.remove(&page), "table page is not currently live");
            state.freed.push(page);
        });
    }
}

// SAFETY: the active arena provides one alignment-preserving address bijection.
unsafe impl DirectMappedAllocator for RebasedAllocator {
    fn direct_map() -> (Range<PhysAddr>, VirtAddr) {
        Arena::active(|arena| {
            let physical = arena.rebased_physical.load(Ordering::Relaxed);
            (
                PhysAddr::from(physical)..PhysAddr::from(physical + arena.len()),
                VirtAddr::from(arena.base),
            )
        })
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        let page = Allocator::allocate_table_page()?;
        Ok(Arena::active(|arena| {
            let physical = arena.rebased_physical.load(Ordering::Relaxed);
            PhysAddr::from(page.bits() - arena.base() + physical)
        }))
    }

    unsafe fn deallocate_table_page(page: PhysAddr) {
        assert_eq!(page.bits() % 4096, 0, "table page is not page-aligned");
        assert!(Self::direct_map().0.contains(&page), "table page is outside the direct map");
        let page = Arena::active(|arena| {
            let physical = arena.rebased_physical.load(Ordering::Relaxed);
            PhysAddr::from(page.bits() - physical + arena.base())
        });
        // SAFETY: undoing the address bijection recovers the original allocated page.
        unsafe { Allocator::deallocate_table_page(page) };
    }
}

/// Four-level paging, the depth most of these tests care about.
#[cfg(feature = "concurrent")]
pub type Table = KernelPageTable<X86Paging<Host>, Allocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
pub type Table = KernelPageTable<X86Paging<Host>, Allocator, Lvl<3>>;

pub const ARENA: usize = 2 * 1024 * 1024;

/// An arena and a table built over it, mapping the arena and nothing else.
pub fn table() -> (Arc<Arena>, Table) {
    let arena = Arena::new(ARENA);
    #[cfg(feature = "concurrent")]
    let table = Table::new(WholeTreeLock::default(), PTEntryFlags::data()).unwrap();
    #[cfg(not(feature = "concurrent"))]
    let table = Table::new(PTEntryFlags::data()).unwrap();
    (arena, table)
}

pub fn flags() -> PTEntryFlags {
    PTEntryFlags::data()
}

pub fn published_bits(word: usize) -> usize {
    if !cfg!(feature = "use_ad") && word & PTEntryFlags::PRESENT.bits() != 0 {
        word | (PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY).bits()
    } else {
        word
    }
}

/// The table pages the root points at.
#[cfg(feature = "concurrent")]
pub fn root_children<S: PagingOwnershipPolicy>(
    table: &PageTable<X86Paging<Host>, Allocator, Lvl<3>, WholeTreeLock, (), S>,
) -> Vec<PhysAddr> {
    (0..512).filter_map(|idx| table.next_table_pa(idx)).collect()
}

#[cfg(not(feature = "concurrent"))]
pub fn root_children<S: PagingOwnershipPolicy>(
    table: &PageTable<X86Paging<Host>, Allocator, Lvl<3>, S>,
) -> Vec<PhysAddr> {
    (0..512).filter_map(|idx| table.next_table_pa(idx)).collect()
}
