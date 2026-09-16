use std::mem::size_of;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::{Lvl, PageLevel};
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::{KernelPageTable, LockAllSpec, LockSpec};
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

use super::common::{Arena, ControllerMemory, MemorySnapshot, Observation, PagingAdapter};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// x86 paging parameters used by the current implementation benchmark.
struct BenchmarkHost;

// SAFETY: the benchmark uses supported x86 flags and never installs or aliases its tables.
unsafe impl X86PagingParams for BenchmarkHost {
    fn private_mask() -> usize {
        0
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(_scope: FlushScope) {}
}

#[derive(Clone)]
/// Adapter from the benchmark arena to the current page-table allocator contract.
struct ArenaAllocator(Arc<Arena>);

// SAFETY: Arena returns unique aligned pages and retains their direct identity mapping.
unsafe impl DirectMappedAllocator for ArenaAllocator {
    fn direct_map(&self) -> std::ops::Range<PhysAddr> {
        PhysAddr::from(self.0.base())..PhysAddr::from(self.0.end())
    }

    fn direct_map_base(&self) -> VirtAddr {
        VirtAddr::from(self.0.base())
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        self.0.allocate_page().map(PhysAddr::from).ok_or(PagingError::AllocFrame)
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        self.0.deallocate_page(paddr.bits());
    }
}

/// One cache-line-isolated reader count for a lock stripe.
#[repr(align(64))]
struct Stripe<T> {
    readers: AtomicUsize,
    content: Mutex<T>,
}

/// Sharded reader state plus the writer flag used by whole-table operations.
struct DomainGate {
    writer: AtomicBool,
}

impl DomainGate {
    fn read<'a, T>(&'a self, stripe: &'a Stripe<T>) -> DomainRead<'a, T> {
        loop {
            while self.writer.load(Ordering::SeqCst) {
                std::hint::spin_loop();
            }
            stripe.readers.fetch_add(1, Ordering::SeqCst);
            if !self.writer.load(Ordering::SeqCst) {
                return DomainRead(stripe);
            }
            stripe.readers.fetch_sub(1, Ordering::SeqCst);
        }
    }

    fn write<'a, T>(&'a self, stripes: &'a [Stripe<T>]) -> DomainWrite<'a> {
        while self
            .writer
            .compare_exchange_weak(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_err()
        {
            std::hint::spin_loop();
        }
        for stripe in stripes {
            while stripe.readers.load(Ordering::SeqCst) != 0 {
                std::hint::spin_loop();
            }
        }
        DomainWrite(self)
    }
}

/// Reader ownership of one page-lock stripe.
struct DomainRead<'a, T>(&'a Stripe<T>);

impl<T> Drop for DomainRead<'_, T> {
    fn drop(&mut self) {
        self.0.readers.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Exclusive ownership of the complete page-lock domain.
struct DomainWrite<'a>(&'a DomainGate);

impl Drop for DomainWrite<'_> {
    fn drop(&mut self) {
        self.0.writer.store(false, Ordering::SeqCst);
    }
}

/// Shared state backing point and whole-domain content locks.
struct StripeDomain<T> {
    gate: DomainGate,
    stripes: Vec<Stripe<T>>,
}

/// Cloneable striped content lock used by the concurrent paging controller.
struct StripedLock<T>(Arc<StripeDomain<T>>);

impl<T> Clone for StripedLock<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Default> StripedLock<T> {
    fn new(stripes: usize) -> Self {
        assert!(stripes > 0);
        Self(Arc::new(StripeDomain {
            gate: DomainGate { writer: AtomicBool::new(false) },
            stripes: (0..stripes)
                .map(|_| Stripe { readers: AtomicUsize::new(0), content: Mutex::new(T::default()) })
                .collect(),
        }))
    }
}

impl<T> StripedLock<T> {
    fn auxiliary_bytes(&self) -> usize {
        2 * size_of::<usize>()
            + size_of::<StripeDomain<T>>()
            + self.0.stripes.capacity() * size_of::<Stripe<T>>()
    }

    fn stripe_index(&self, page: PhysAddr) -> usize {
        let mut key = page.bits() / 4096;
        key ^= key >> 16;
        key = key.wrapping_mul(0x21f0_aaad);
        key ^= key >> 15;
        key = key.wrapping_mul(0x735a_2d97);
        key ^= key >> 15;
        key % self.0.stripes.len()
    }
}

/// Point lock guard that retains both stripe and domain ownership.
pub struct PointGuard<'a, T> {
    stripe: MutexGuard<'a, T>,
    _domain: DomainRead<'a, T>,
}

impl<T> Deref for PointGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.stripe
    }
}

impl<T> DerefMut for PointGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.stripe
    }
}

// SAFETY: each key has a stable stripe, and its reader count excludes lock_all.
unsafe impl<T> LockSpec<T> for StripedLock<T> {
    type Guard<'a>
        = PointGuard<'a, T>
    where
        Self: 'a,
        T: 'a;

    fn lock(&self, page: PhysAddr) -> Self::Guard<'_> {
        let stripe = &self.0.stripes[self.stripe_index(page)];
        let domain = self.0.gate.read(stripe);
        let stripe = stripe.content.lock().unwrap();
        PointGuard { stripe, _domain: domain }
    }
}

// SAFETY: the writer waits for every stripe's readers and excludes new point guards.
unsafe impl<T> LockAllSpec<T> for StripedLock<T> {
    type AllGuard<'a>
        = DomainWrite<'a>
    where
        Self: 'a,
        T: 'a;

    fn lock_all(&self) -> Self::AllGuard<'_> {
        self.0.gate.write(&self.0.stripes)
    }
}

type Table = KernelPageTable<X86Paging<BenchmarkHost>, ArenaAllocator, Lvl<3>, StripedLock<()>>;

/// Current paging implementation with benchmark-owned allocation and locking.
pub struct CurrentAdapter {
    table: Table,
    arena: Arc<Arena>,
    lock_bytes: usize,
}

// SAFETY: the concurrent controller uses atomic entries and the adapter's content-lock domain.
unsafe impl Send for CurrentAdapter {}
unsafe impl Sync for CurrentAdapter {}

fn flags(writable: bool) -> PTEntryFlags {
    let flags =
        PTEntryFlags::PRESENT | PTEntryFlags::USER | PTEntryFlags::NX | PTEntryFlags::ACCESSED;
    if writable {
        flags | PTEntryFlags::WRITABLE | PTEntryFlags::DIRTY
    } else {
        flags
    }
}

impl PagingAdapter for CurrentAdapter {
    const NAME: &'static str = "paging-current";

    fn new(arena_pages: usize, stripes: usize) -> Self {
        let arena = Arena::new(arena_pages);
        let lock = StripedLock::new(stripes);
        let lock_bytes = lock.auxiliary_bytes();
        let table = Table::new(ArenaAllocator(arena.clone()), lock, PTEntryFlags::data())
            .expect("create current page table");
        Self { table, arena, lock_bytes }
    }

    fn map_4k(&self, virtual_address: u64, physical_address: u64) {
        self.table
            .map_4k(
                VirtAddr::from(virtual_address as usize),
                PhysAddr::from(physical_address as usize),
                flags(true),
                false,
            )
            .expect("current map_4k");
    }

    fn map_2m(&self, virtual_address: u64, physical_address: u64) {
        self.table
            .map_2m(
                VirtAddr::from(virtual_address as usize),
                PhysAddr::from(physical_address as usize),
                flags(true),
                false,
            )
            .expect("current map_2m");
    }

    fn unmap_4k(&self, virtual_address: u64) {
        let (_, flush) =
            self.table.unmap_4k(VirtAddr::from(virtual_address as usize)).expect("current unmap");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn translate(&self, virtual_address: u64) -> Option<u64> {
        self.table
            .phys_addr(VirtAddr::from(virtual_address as usize))
            .ok()
            .map(|address| address.bits() as u64)
    }

    fn observe(&self, virtual_address: u64) -> Option<Observation> {
        let address = VirtAddr::from(virtual_address as usize);
        let snapshot = self.table.walk(address);
        let entry = snapshot.read();
        if !entry.is_leaf(snapshot.level()) {
            return None;
        }
        let translation = self.table.translate(address).expect("current translate");
        Some(Observation {
            physical: translation.address().bits() as u64,
            page_size: snapshot.level().size() as u64,
            writable: entry.writable(),
            user: entry.user(),
            executable: !entry.flags().contains(PTEntryFlags::NX),
        })
    }

    fn protect_4k(&self, virtual_address: u64, writable: bool) {
        let flush = self
            .table
            .mprotect(
                VirtAddr::from(virtual_address as usize),
                PageLevel::Level0,
                flags(writable),
                false,
            )
            .expect("current mprotect");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn split_2m_to_4k(&self, virtual_address: u64) {
        let flush = self
            .table
            .split(VirtAddr::from(virtual_address as usize), PageLevel::Level0, false)
            .expect("current split");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn protect_range(&self, start: u64, end: u64, writable: bool) {
        let (result, flush) = self.table.mprotect_range(
            VirtAddr::from(start as usize),
            VirtAddr::from(end as usize),
            flags(writable),
            false,
        );
        result.expect("current mprotect_range");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn reset_peak(&self) {
        self.arena.reset_peak();
    }

    fn memory(&self) -> MemorySnapshot {
        self.arena.memory()
    }

    fn controller_memory(&self) -> ControllerMemory {
        ControllerMemory { inline_bytes: size_of::<Self>(), auxiliary_bytes: self.lock_bytes }
    }
}
