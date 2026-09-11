//! A page table over host memory, so the tests can walk a real tree.
//!
//! The arena is a leaked, 2 MiB-aligned buffer, and the handler direct-maps it
//! identically: a physical address in it is a host address the walk can
//! dereference. Each test builds its own arena, so the tests do not share an
//! allocator.
//!
//! Run them on a target that can execute:
//! `cargo test -p paging --target x86_64-unknown-linux-gnu`.
#![allow(dead_code)]

use std::sync::{Arc, Mutex};

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::Lvl;
use paging::os_contract::{DirectMappedPagingHandler, PagingError};
use paging::pagetable::PageTable;
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

/// Unencrypted memory whose TLB needs no invalidating: the host's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Host;

impl X86PagingParams for Host {
    fn private_mask() -> usize {
        0
    }

    fn flush_tlb_global_sync(_scope: FlushScope) {}
}

/// A bump allocator over one leaked buffer, which remembers what was freed.
pub struct Arena {
    base: usize,
    len: usize,
    next: Mutex<usize>,
    freed: Mutex<Vec<usize>>,
}

impl Arena {
    pub fn new(len: usize) -> Arc<Self> {
        assert!(len.is_power_of_two());
        let buf = vec![0u8; len * 2].leak();
        let base = (buf.as_ptr() as usize + len - 1) & !(len - 1);
        Arc::new(Self { base, len, next: Mutex::new(base), freed: Mutex::new(Vec::new()) })
    }

    pub fn base(&self) -> usize {
        self.base
    }

    pub fn len(&self) -> usize {
        self.len
    }

    /// How many pages have been handed out.
    pub fn allocated(&self) -> usize {
        (*self.next.lock().unwrap() - self.base) / 4096
    }

    pub fn freed(&self) -> Vec<usize> {
        self.freed.lock().unwrap().clone()
    }

    pub fn clear_freed(&self) {
        self.freed.lock().unwrap().clear();
    }
}

/// The arena as a direct map: identity, so a walk can follow it on the host.
#[derive(Clone)]
pub struct Handler(pub Arc<Arena>);

unsafe impl DirectMappedPagingHandler for Handler {
    fn direct_map(&self) -> core::ops::Range<PhysAddr> {
        PhysAddr::from(self.0.base)..PhysAddr::from(self.0.base + self.0.len)
    }

    fn direct_map_base(&self) -> VirtAddr {
        VirtAddr::from(self.0.base)
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        let mut next = self.0.next.lock().unwrap();
        if *next + 4096 > self.0.base + self.0.len {
            return Err(PagingError::AllocFrame);
        }
        let page = *next;
        *next += 4096;
        // SAFETY: the page is inside the arena and nothing else holds it.
        unsafe { core::ptr::write_bytes(page as *mut u8, 0, 4096) };
        Ok(PhysAddr::from(page))
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        assert!((self.0.base..self.0.base + self.0.len).contains(&paddr.bits()));
        self.0.freed.lock().unwrap().push(paddr.bits());
    }
}

/// Four-level paging, the depth most of these tests care about.
pub type Table = PageTable<X86Paging<Host>, Handler, Lvl<3>>;

pub const ARENA: usize = 2 * 1024 * 1024;

/// An arena and a table built over it, mapping the arena and nothing else.
pub fn table() -> (Arc<Arena>, Table) {
    let arena = Arena::new(ARENA);
    let table = Table::new(Handler(arena.clone()), PTEntryFlags::data()).unwrap();
    (arena, table)
}

pub fn flags() -> PTEntryFlags {
    PTEntryFlags::data()
}

/// The table pages the root points at.
pub fn root_children(table: &Table) -> Vec<PhysAddr> {
    (0..512).filter_map(|idx| table.next_table_pa(idx)).collect()
}
