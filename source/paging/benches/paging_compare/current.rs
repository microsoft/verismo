use std::mem::size_of;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::level::{Lvl, PageLevel};
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::pagetable::{KernelPageTable, LockSpec};
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

/// Adapter from the benchmark arena to the current page-table allocator contract.
struct ArenaAllocator;

static CURRENT_ARENA: AtomicPtr<Arena> = AtomicPtr::new(std::ptr::null_mut());

impl ArenaAllocator {
    fn arena() -> &'static Arena {
        let arena = CURRENT_ARENA.load(Ordering::Relaxed);
        assert!(!arena.is_null(), "benchmark arena is not installed");
        // SAFETY: CurrentAdapter retains the Arc while its table can call the allocator.
        unsafe { &*arena }
    }
}

// SAFETY: Arena returns unique aligned pages and retains their direct identity mapping.
unsafe impl DirectMappedAllocator for ArenaAllocator {
    #[inline(always)]
    fn direct_map() -> (std::ops::Range<PhysAddr>, VirtAddr) {
        let arena = Self::arena();
        (PhysAddr::from(arena.base())..PhysAddr::from(arena.end()), VirtAddr::from(arena.base()))
    }

    #[inline(always)]
    fn resolve_paddr(paddr: PhysAddr) -> VirtAddr {
        VirtAddr::from(paddr.bits())
    }

    #[inline(always)]
    fn resolve_vaddr(vaddr: VirtAddr) -> PhysAddr {
        PhysAddr::from(vaddr.bits())
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        Self::arena().allocate_page().map(PhysAddr::from).ok_or(PagingError::AllocFrame)
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        Self::arena().deallocate_page(paddr.bits());
    }
}

/// Arena-indexed page locks matching the VeriOS benchmark host.
struct ArenaPageLock(Arc<Arena>);

impl Clone for ArenaPageLock {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

/// Exclusive ownership of one arena page lock.
struct ArenaPageGuard<'a> {
    arena: &'a Arena,
    address: usize,
    content: (),
}

impl Deref for ArenaPageGuard<'_> {
    type Target = ();

    fn deref(&self) -> &() {
        &self.content
    }
}

impl DerefMut for ArenaPageGuard<'_> {
    fn deref_mut(&mut self) -> &mut () {
        &mut self.content
    }
}

impl Drop for ArenaPageGuard<'_> {
    fn drop(&mut self) {
        self.arena.unlock_page(self.address);
    }
}

// SAFETY: each arena page has one stable lock shared by all users of the arena.
unsafe impl LockSpec<()> for ArenaPageLock {
    type Guard<'a>
        = ArenaPageGuard<'a>
    where
        Self: 'a;

    fn lock(&self, page: PhysAddr) -> Self::Guard<'_> {
        let address = page.bits();
        self.0.lock_page(address);
        ArenaPageGuard { arena: &self.0, address, content: () }
    }
}

type Table = KernelPageTable<X86Paging<BenchmarkHost>, ArenaAllocator, Lvl<3>, ArenaPageLock>;

/// Current paging implementation with benchmark-owned allocation and locking.
pub struct CurrentAdapter {
    table: Table,
    arena: Arc<Arena>,
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

    fn new(arena_pages: usize) -> Self {
        let arena = Arena::new(arena_pages);
        CURRENT_ARENA.store(Arc::as_ptr(&arena).cast_mut(), Ordering::Relaxed);
        let lock = ArenaPageLock(arena.clone());
        let table = Table::new(lock, PTEntryFlags::data()).expect("create current page table");
        Self { table, arena }
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

    #[inline(always)]
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
        ControllerMemory { inline_bytes: size_of::<Self>(), auxiliary_bytes: 0 }
    }
}
