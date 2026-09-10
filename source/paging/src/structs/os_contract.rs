//! What an embedder owes the page table: allocation, the direct map, and TLB
//! invalidation. The page table allocates no memory and knows no virtual memory
//! layout of its own.
use crate::structs::address::{PhysAddr, VirtAddr};

/// Why an operation could not be carried out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PagingError {
    /// No frame was available for an intermediate table.
    AllocFrame,
    /// The walk found no mapping for the address.
    NotMapped,
    /// A mapping is already installed where one was asked for.
    EntryAlreadyPresent,
    /// The tree is not deep enough for the requested page size.
    InvalidLevel,
    /// A table pointer sits where a mapping was expected. Overwriting one would
    /// strand the subtree below it, so no operation on a leaf will.
    NotLeafEntry,
}

/// OS-level page table services, provided by a value the table holds: an
/// embedder that needs allocator or address-space state can keep it there.
///
/// # Safety
///
/// * `paddr_to_vaddr` maps `paddr` writably for as long as the table lives, and
///   inverts `vaddr_to_paddr`. Addresses passed to it are always clean.
/// * `allocate_table_page` returns a unique, page-aligned, zeroed frame with a
///   clean address that `paddr_to_vaddr` can map.
/// * `deallocate_table_page` is given only frames that no table links to.
pub unsafe trait PagingHandler: 'static {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr;

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr;

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError>;

    /// # Safety
    ///
    /// `paddr` must come from [`Self::allocate_table_page`] and be linked into
    /// no tree.
    unsafe fn deallocate_table_page(&self, paddr: PhysAddr);
}
