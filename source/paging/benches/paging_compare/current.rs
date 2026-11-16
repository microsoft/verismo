use std::mem::size_of;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::Arc;

use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    pagetable::{KernelPageTable, PagingMutex},
    structs::{DirectMappedAllocator, Huge, Lvl, Page, PageSize, PagingError, PhysFrame, Regular},
};

use super::common::{Arena, ControllerMemory, MemorySnapshot, Observation, PagingAdapter};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// x86 paging parameters used by the current implementation benchmark.
struct BenchmarkHost;

// SAFETY: the benchmark uses supported x86 flags and never installs or aliases its tables.
unsafe impl X86_64PagingParams for BenchmarkHost {
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

    fn allocate_zeroed_table_page() -> Result<PhysAddr, PagingError> {
        Self::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        Self::arena().deallocate_page(paddr.bits());
    }
}

type Table = KernelPageTable<X86_64Paging<BenchmarkHost>, ArenaAllocator, Lvl<3>>;

/// Current paging implementation with benchmark-owned allocation and cfg-selected locking.
pub struct CurrentAdapter {
    table: Table,
    arena: Arc<Arena>,
}

// SAFETY: the concurrent controller uses atomic entries and stable built-in content locks.
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
    #[cfg(all(not(feature = "spin-mutex"), not(feature = "striped-locks")))]
    const NAME: &'static str = "paging-current-ticket-global";
    #[cfg(all(feature = "spin-mutex", not(feature = "striped-locks")))]
    const NAME: &'static str = "paging-current-spin-global";
    #[cfg(all(not(feature = "spin-mutex"), feature = "striped-locks"))]
    const NAME: &'static str = "paging-current-ticket-striped";
    #[cfg(all(feature = "spin-mutex", feature = "striped-locks"))]
    const NAME: &'static str = "paging-current-spin-striped";

    fn new(arena_pages: usize) -> Self {
        let arena = Arena::new(arena_pages);
        CURRENT_ARENA.store(Arc::as_ptr(&arena).cast_mut(), Ordering::Relaxed);
        let table = Table::new(PTEntryFlags::data()).expect("create current page table");
        Self { table, arena }
    }

    fn map_4k(&self, virtual_address: u64, physical_address: u64) {
        self.table
            .map(
                Page::<Regular>::from_start_address(VirtAddr::from(virtual_address as usize))
                    .unwrap(),
                PhysFrame::<Regular>::from_start_address(PhysAddr::from(physical_address as usize))
                    .unwrap(),
                flags(true),
                false,
            )
            .expect("current map_4k");
    }

    fn map_2m(&self, virtual_address: u64, physical_address: u64) {
        self.table
            .map(
                Page::<Huge>::from_start_address(VirtAddr::from(virtual_address as usize)).unwrap(),
                PhysFrame::<Huge>::from_start_address(PhysAddr::from(physical_address as usize))
                    .unwrap(),
                flags(true),
                false,
            )
            .expect("current map_2m");
    }

    fn map_range(&self, start: u64, end: u64, physical_start: u64) {
        let start = VirtAddr::from(start as usize);
        let end = VirtAddr::from(end as usize);
        let range = Page::<Regular>::range_inclusive(
            Page::from_start_address(start).unwrap(),
            Page::from_start_address(end - Regular::SIZE).unwrap(),
        );
        let mut frames = (0..range.len()).map(|offset| {
            PhysFrame::from_start_address(PhysAddr::from(
                physical_start as usize + offset * Regular::SIZE,
            ))
            .unwrap()
        });
        self.table.map_region(range, &mut frames, flags(true)).expect("current map_region");
    }

    #[inline(always)]
    fn unmap_4k(&self, virtual_address: u64) {
        let (_, flush) = self
            .table
            .unmap(
                Page::<Regular>::from_start_address(VirtAddr::from(virtual_address as usize))
                    .unwrap(),
                None,
            )
            .expect("current unmap");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn unmap_range(&self, start: u64, end: u64) {
        let (all_mapped, flush) = self
            .table
            .unmap_region(VirtAddr::from(start as usize), VirtAddr::from(end as usize))
            .expect("current unmap_region");
        assert!(all_mapped);
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
        if !entry.is_present_leaf(snapshot.level()) {
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

    #[inline(always)]
    fn protect_4k(&self, virtual_address: u64, writable: bool) {
        let flush = self
            .table
            .set_flags(
                Page::<Regular>::from_start_address(VirtAddr::from(virtual_address as usize))
                    .unwrap(),
                flags(writable),
                false,
            )
            .expect("current set_flags");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn split_2m_to_4k(&self, virtual_address: u64) {
        let flush = self
            .table
            .split(
                Page::<Huge>::containing_address(VirtAddr::from(virtual_address as usize)),
                false,
            )
            .expect("current split");
        // SAFETY: benchmark tables are never installed in hardware page-table roots.
        unsafe { flush.ignore() };
    }

    fn protect_range(&self, start: u64, end: u64, writable: bool) {
        let (result, flush) = self.table.set_flags_range(
            VirtAddr::from(start as usize),
            VirtAddr::from(end as usize),
            flags(writable),
            false,
        );
        result.expect("current set_flags_range");
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
        let lock_count = if cfg!(feature = "striped-locks") { 64 } else { 1 };
        ControllerMemory {
            inline_bytes: size_of::<Self>(),
            auxiliary_bytes: lock_count * size_of::<PagingMutex<()>>(),
        }
    }
}

#[no_mangle]
#[inline(never)]
pub fn paging_current_translate_codegen(
    adapter: &CurrentAdapter,
    virtual_address: u64,
) -> Option<u64> {
    adapter.translate(virtual_address)
}
