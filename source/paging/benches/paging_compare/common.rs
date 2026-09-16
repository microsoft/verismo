use std::alloc::{alloc_zeroed, dealloc, Layout};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::Arc;

pub const PAGE_SIZE: u64 = 4096;
pub const HUGE_SIZE: u64 = 2 * 1024 * 1024;
pub const ADDRESS_MASK: u64 = 0x000f_ffff_ffff_f000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Canonical mapping state used for cross-adapter validation.
pub struct Observation {
    pub physical: u64,
    pub page_size: u64,
    pub writable: bool,
    pub user: bool,
    pub executable: bool,
}

#[derive(Clone, Copy, Debug)]
/// Exact page-table allocation state at one instant.
pub struct MemorySnapshot {
    pub live_pages: usize,
    pub peak_pages: usize,
}

#[derive(Clone, Copy, Debug)]
/// Persistent controller memory outside allocated page-table pages.
pub struct ControllerMemory {
    pub inline_bytes: usize,
    pub auxiliary_bytes: usize,
}

/// One page lock isolated from locks used by unrelated table pages.
#[repr(align(64))]
struct PageLock(AtomicBool);

/// Common operation surface implemented by every compared page table.
pub trait PagingAdapter: Send + Sync + Sized + 'static {
    const NAME: &'static str;

    fn new(arena_pages: usize) -> Self;
    fn map_4k(&self, virtual_address: u64, physical_address: u64);
    fn map_2m(&self, virtual_address: u64, physical_address: u64);
    fn unmap_4k(&self, virtual_address: u64);
    fn translate(&self, virtual_address: u64) -> Option<u64>;
    fn observe(&self, virtual_address: u64) -> Option<Observation>;
    fn protect_4k(&self, virtual_address: u64, writable: bool);
    fn split_2m_to_4k(&self, virtual_address: u64);
    fn protect_range(&self, start: u64, end: u64, writable: bool);
    fn reset_peak(&self);
    fn memory(&self) -> MemorySnapshot;
    fn controller_memory(&self) -> ControllerMemory;
}

/// Prefaulted aligned storage with exact page and lock accounting.
pub struct Arena {
    base: *mut u8,
    layout: Layout,
    capacity: usize,
    next: AtomicUsize,
    live: AtomicUsize,
    peak: AtomicUsize,
    states: Box<[AtomicU8]>,
    page_locks: Box<[PageLock]>,
}

// SAFETY: allocation lifetime is shared through Arc and all mutable state is atomic.
unsafe impl Send for Arena {}
// SAFETY: allocation lifetime is shared through Arc and all mutable state is atomic.
unsafe impl Sync for Arena {}

impl Arena {
    pub fn new(capacity: usize) -> Arc<Self> {
        let bytes = capacity.checked_mul(PAGE_SIZE as usize).expect("arena size overflow");
        let layout = Layout::from_size_align(bytes, PAGE_SIZE as usize).expect("arena layout");
        // SAFETY: `layout` is nonzero and retained for the matching deallocation.
        let base = unsafe { alloc_zeroed(layout) };
        assert!(!base.is_null(), "page-table arena allocation failed");
        assert!((base as u64) < (1u64 << 52), "arena is above the x86-64 address field");
        for index in 0..capacity {
            // SAFETY: every offset selects the first byte of an allocated arena page.
            unsafe { base.add(index * PAGE_SIZE as usize).write_volatile(0) };
        }
        Arc::new(Self {
            base,
            layout,
            capacity,
            next: AtomicUsize::new(0),
            live: AtomicUsize::new(0),
            peak: AtomicUsize::new(0),
            states: (0..capacity).map(|_| AtomicU8::new(0)).collect(),
            page_locks: (0..capacity).map(|_| PageLock(AtomicBool::new(false))).collect(),
        })
    }

    pub fn base(&self) -> usize {
        self.base as usize
    }

    pub fn end(&self) -> usize {
        self.base() + self.layout.size()
    }

    pub fn allocate_page(&self) -> Option<usize> {
        let index = self.next.fetch_add(1, Ordering::Relaxed);
        if index >= self.capacity {
            return None;
        }
        assert_eq!(
            self.states[index].compare_exchange(0, 1, Ordering::AcqRel, Ordering::Acquire),
            Ok(0),
            "arena page allocated twice"
        );
        let address = self.page_address(index);
        // SAFETY: the successful state transition gives this allocation exclusive ownership.
        unsafe { std::ptr::write_bytes(address as *mut u8, 0, PAGE_SIZE as usize) };
        let live = self.live.fetch_add(1, Ordering::AcqRel) + 1;
        self.peak.fetch_max(live, Ordering::Relaxed);
        Some(address)
    }

    pub fn deallocate_page(&self, address: usize) {
        let index = self.index_of(address);
        assert_eq!(self.states[index].swap(0, Ordering::AcqRel), 1, "arena page freed twice");
        self.live.fetch_sub(1, Ordering::AcqRel);
    }

    pub fn index_of(&self, address: usize) -> usize {
        let offset = address.checked_sub(self.base()).expect("page below arena");
        assert_eq!(offset % PAGE_SIZE as usize, 0, "unaligned arena page");
        let index = offset / PAGE_SIZE as usize;
        assert!(index < self.capacity, "page above arena");
        index
    }

    pub fn lock_page(&self, address: usize) {
        let lock = &self.page_locks[self.index_of(address)];
        while lock
            .0
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            std::hint::spin_loop();
        }
    }

    pub fn unlock_page(&self, address: usize) {
        self.page_locks[self.index_of(address)].0.store(false, Ordering::Release);
    }

    pub fn reset_page_lock(&self, address: usize) {
        self.page_locks[self.index_of(address)].0.store(false, Ordering::Release);
    }

    pub fn reset_peak(&self) {
        self.peak.store(self.live.load(Ordering::Acquire), Ordering::Release);
    }

    pub fn memory(&self) -> MemorySnapshot {
        MemorySnapshot {
            live_pages: self.live.load(Ordering::Acquire),
            peak_pages: self.peak.load(Ordering::Acquire),
        }
    }

    fn page_address(&self, index: usize) -> usize {
        self.base() + index * PAGE_SIZE as usize
    }
}

impl Drop for Arena {
    fn drop(&mut self) {
        // SAFETY: `base` was allocated with this layout and the final Arc owns it.
        unsafe { dealloc(self.base, self.layout) };
    }
}
