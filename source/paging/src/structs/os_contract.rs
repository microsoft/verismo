//! What an embedder owes the page table: allocation, the direct map, and TLB
//! invalidation. The page table allocates no memory and knows no virtual memory
//! layout of its own.
use core::ops::Range;

use crate::structs::address::{Address, PhysAddr, VirtAddr};

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
    /// The tree does not map one of its own table pages at the address the
    /// handler hands out for that page.
    TablePageNotSelfMapped,
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

/// A handler whose memory is reachable at a fixed offset from its physical
/// address, which is what a kernel's direct map gives. Implementing it is
/// enough to be a [`PagingHandler`].
///
/// # Safety
///
/// The obligations of [`PagingHandler`] carry over, and `direct_map` must
/// report the region `allocate_table_page` draws from: a table built over the
/// region can then reach every page it is given.
pub unsafe trait DirectMappedPagingHandler: 'static {
    /// The physical region the handler allocates from and maps as one piece.
    fn direct_map(&self) -> Range<PhysAddr>;

    /// Where the first address of [`Self::direct_map`] is reachable.
    fn direct_map_base(&self) -> VirtAddr;

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError>;

    /// # Safety
    ///
    /// `paddr` must come from [`Self::allocate_table_page`] and be linked into
    /// no tree.
    unsafe fn deallocate_table_page(&self, paddr: PhysAddr);
}

// SAFETY: the offset is fixed, so the two translations invert each other, and
// the rest is deferred to an implementation that owes the same obligations.
unsafe impl<T: DirectMappedPagingHandler> PagingHandler for T {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        let offset = paddr.bits() - self.direct_map().start.bits();
        self.direct_map_base() + offset
    }

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        let offset = vaddr.bits() - self.direct_map_base().bits();
        self.direct_map().start + offset
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        <T as DirectMappedPagingHandler>::allocate_table_page(self)
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        // SAFETY: the caller's obligation is the same in both traits.
        unsafe { <T as DirectMappedPagingHandler>::deallocate_table_page(self, paddr) }
    }
}
