//! A page table over host memory, so the tests can walk a real tree.
//!
//! The arena is a leaked, 2 MiB-aligned buffer, and the allocator direct-maps it
//! identically: a physical address in it is a host address the walk can
//! dereference. Each test builds its own arena, so the tests do not share an
//! allocator.
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
use std::sync::{Arc, Mutex};

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::Lvl;
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::{KernelPageTable, PageTable};
#[cfg(feature = "concurrent")]
use paging::pagetable::{LockAllSpec, LockSpec};
use paging::policy::PagingPolicy;
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
    state: Mutex<ArenaState>,
}

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
        Arc::new(Self {
            base,
            len,
            state: Mutex::new(ArenaState { next: base, live: BTreeSet::new(), freed: Vec::new() }),
        })
    }

    pub fn base(&self) -> usize {
        self.base
    }

    pub fn len(&self) -> usize {
        self.len
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
}

/// The arena as a direct map: identity, so a walk can follow it on the host.
#[derive(Clone)]
pub struct Allocator(pub Arc<Arena>);

#[derive(Clone)]
pub struct RebasedAllocator {
    pub inner: Allocator,
    pub physical_base: usize,
}

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
    fn direct_map(&self) -> core::ops::Range<PhysAddr> {
        PhysAddr::from(self.0.base)..PhysAddr::from(self.0.base + self.0.len)
    }

    fn direct_map_base(&self) -> VirtAddr {
        VirtAddr::from(self.0.base)
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        let mut state = self.0.state.lock().unwrap();
        if state.next + 4096 > self.0.base + self.0.len {
            return Err(PagingError::AllocFrame);
        }
        let page = state.next;
        state.next += 4096;
        assert!(state.live.insert(page));
        // SAFETY: this private arena page is poisoned to expose missing initialization.
        unsafe { core::ptr::write_bytes(page as *mut u8, 0xff, 4096) };
        Ok(PhysAddr::from(page))
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        let page = paddr.bits();
        assert_eq!(page % 4096, 0, "table page is not page-aligned");
        assert!(
            (self.0.base..self.0.base + self.0.len).contains(&page),
            "table page is outside the arena"
        );
        let mut state = self.0.state.lock().unwrap();
        assert!(page < state.next, "table page was not allocated by this arena");
        assert!(state.live.remove(&page), "table page is not currently live");
        state.freed.push(page);
    }
}

// SAFETY: clones share the arena and its alignment-preserving address bijection.
unsafe impl DirectMappedAllocator for RebasedAllocator {
    fn direct_map(&self) -> Range<PhysAddr> {
        PhysAddr::from(self.physical_base)..PhysAddr::from(self.physical_base + self.inner.0.len())
    }

    fn direct_map_base(&self) -> VirtAddr {
        self.inner.direct_map_base()
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        self.inner
            .allocate_table_page()
            .map(|page| PhysAddr::from(page.bits() - self.inner.0.base() + self.physical_base))
    }

    unsafe fn deallocate_table_page(&self, page: PhysAddr) {
        assert_eq!(page.bits() % 4096, 0, "table page is not page-aligned");
        assert!(self.direct_map().contains(&page), "table page is outside the direct map");
        let page = PhysAddr::from(page.bits() - self.physical_base + self.inner.0.base());
        // SAFETY: undoing the address bijection recovers the original allocated page.
        unsafe { self.inner.deallocate_table_page(page) };
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
    let table =
        Table::new(Allocator(arena.clone()), WholeTreeLock::default(), PTEntryFlags::data())
            .unwrap();
    #[cfg(not(feature = "concurrent"))]
    let table = Table::new(Allocator(arena.clone()), PTEntryFlags::data()).unwrap();
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
pub fn root_children<S: PagingPolicy>(
    table: &PageTable<X86Paging<Host>, Allocator, Lvl<3>, WholeTreeLock, (), S>,
) -> Vec<PhysAddr> {
    (0..512).filter_map(|idx| table.next_table_pa(idx)).collect()
}

#[cfg(not(feature = "concurrent"))]
pub fn root_children<S: PagingPolicy>(
    table: &PageTable<X86Paging<Host>, Allocator, Lvl<3>, S>,
) -> Vec<PhysAddr> {
    (0..512).filter_map(|idx| table.next_table_pa(idx)).collect()
}
