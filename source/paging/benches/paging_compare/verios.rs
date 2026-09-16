use std::mem::size_of;
use std::sync::Arc;

use pgtable::arch::current::flags::PteFlags;
use pgtable::frontend::PageTable;
use pgtable::level::{PageSize, L4};
use pgtable::pt_entry::{leaf_field, Conf, EntryPolicy};
use pgtable::pt_page::PtPageOps;

use super::common::{
    Arena, ControllerMemory, MemorySnapshot, Observation, PagingAdapter, ADDRESS_MASK,
};

/// Verios host operations backed by the shared benchmark arena.
struct VeriosHost {
    arena: Arc<Arena>,
}

impl EntryPolicy for VeriosHost {
    fn private_mask(&self) -> u64 {
        0
    }

    fn shared_mask(&self) -> u64 {
        0
    }

    fn table_flags(&self) -> u64 {
        leaf_flags(true).without(PteFlags::NO_EXECUTE).bits()
    }
}

impl PtPageOps for VeriosHost {
    fn alloc(&self, _hint: u64, _level: u32) -> Option<(*mut u64, u64)> {
        let address = self.arena.allocate_page()?;
        Some((address as *mut u64, address as u64))
    }

    fn free(&self, va: *mut u64, _pa: u64, _level: u32) {
        let address = va as usize;
        self.arena.reset_page_lock(address);
        self.arena.deallocate_page(address);
    }

    fn lock(&self, base: *mut u64, _level: u32) {
        self.arena.lock_page(base as usize);
    }

    fn unlock(&self, base: *mut u64, _level: u32) {
        self.arena.unlock_page(base as usize);
    }

    fn child_base(&self, field: u64) -> *mut u64 {
        (field & ADDRESS_MASK) as *mut u64
    }
}

fn leaf_flags(writable: bool) -> PteFlags {
    let flags = PteFlags::PRESENT
        .with(PteFlags::USER_ACCESSIBLE)
        .with(PteFlags::NO_EXECUTE)
        .with(PteFlags::ACCESSED);
    if writable {
        flags.with(PteFlags::WRITABLE).with(PteFlags::DIRTY)
    } else {
        flags
    }
}

/// Pinned verios-pagetable implementation under test.
pub struct VeriosAdapter {
    table: PageTable<L4>,
    host: VeriosHost,
}

impl PagingAdapter for VeriosAdapter {
    const NAME: &'static str = "verios-b21b173";

    fn new(arena_pages: usize) -> Self {
        let arena = Arena::new(arena_pages);
        let host = VeriosHost { arena };
        let root = host.arena.allocate_page().expect("verios root") as *mut u64;
        // SAFETY: the fresh root is aligned, zeroed, uniquely owned, and arena-backed.
        let table = unsafe { PageTable::adopt(&host, root) };
        Self { table, host }
    }

    fn map_4k(&self, virtual_address: u64, physical_address: u64) {
        self.table
            .map(
                &self.host,
                virtual_address,
                physical_address,
                leaf_flags(true),
                Conf::Private,
                PageSize::Size4K,
            )
            .expect("verios map_4k");
    }

    fn map_2m(&self, virtual_address: u64, physical_address: u64) {
        self.table
            .map(
                &self.host,
                virtual_address,
                physical_address,
                leaf_flags(true),
                Conf::Private,
                PageSize::Size2M,
            )
            .expect("verios map_2m");
    }

    fn unmap_4k(&self, virtual_address: u64) {
        self.table.unmap(&self.host, virtual_address, PageSize::Size4K).expect("verios unmap");
    }

    fn translate(&self, virtual_address: u64) -> Option<u64> {
        let (word, depth) = self.table.query(&self.host, virtual_address).ok()?;
        Some(leaf_field(depth, word) + (virtual_address & ((1u64 << (12 + 9 * (depth - 1))) - 1)))
    }

    fn observe(&self, virtual_address: u64) -> Option<Observation> {
        let (word, depth) = self.table.query(&self.host, virtual_address).ok()?;
        Some(Observation {
            physical: leaf_field(depth, word)
                + (virtual_address & ((1u64 << (12 + 9 * (depth - 1))) - 1)),
            page_size: 1u64 << (12 + 9 * (depth - 1)),
            writable: word & PteFlags::WRITABLE.bits() != 0,
            user: word & PteFlags::USER_ACCESSIBLE.bits() != 0,
            executable: word & PteFlags::NO_EXECUTE.bits() == 0,
        })
    }

    fn protect_4k(&self, virtual_address: u64, writable: bool) {
        self.table
            .protect(&self.host, virtual_address, leaf_flags(writable), PageSize::Size4K)
            .expect("verios protect");
    }

    fn split_2m_to_4k(&self, virtual_address: u64) {
        pgtable::pt_ops::split::split_l4(
            &self.host,
            self.table.root(),
            virtual_address,
            PageSize::Size2M,
        )
        .expect("verios split_l4");
    }

    fn protect_range(&self, start: u64, end: u64, writable: bool) {
        self.table
            .protect_range(&self.host, start..end, leaf_flags(writable))
            .expect("verios protect_range");
    }

    fn reset_peak(&self) {
        self.host.arena.reset_peak();
    }

    fn memory(&self) -> MemorySnapshot {
        self.host.arena.memory()
    }

    fn controller_memory(&self) -> ControllerMemory {
        ControllerMemory { inline_bytes: size_of::<Self>(), auxiliary_bytes: 0 }
    }
}
