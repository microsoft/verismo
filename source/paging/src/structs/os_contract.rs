//! What an embedder owes the page table: allocation, the direct map, and TLB
//! invalidation. The page table allocates no memory and knows no virtual memory
//! layout of its own.
use core::ops::Range;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::level::PageLevel;

/// Why an operation could not be carried out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PagingError {
    /// No frame was available for an intermediate table.
    AllocFrame,
    /// The walk found no mapping for the address.
    NotMapped,
    /// A mapping is already installed where one was asked for, of `level` and
    /// onto `frame`. A caller that wanted that very mapping can tell from the
    /// frame that it has nothing to do.
    EntryAlreadyPresent { frame: PhysAddr, level: PageLevel },
    /// The tree is not deep enough for the requested page size.
    InvalidLevel,
    /// An address does not satisfy the requested page alignment.
    InvalidAddress,
    /// A range is reversed or not aligned to the smallest page size.
    InvalidRange,
    /// The requested protection flags would remove a mapping.
    InvalidFlags,
    /// This controller may not mutate the requested kernel mappings.
    PermissionDenied,
    /// The tree does not map one of its own table pages at the address the
    /// allocator hands out for that page.
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
/// * Clones refer to the same allocator and address-space mapping. A frame
///   allocated through one clone can be resolved and freed through another.
///   Each clone must retain the backing state needed for those operations.
/// * `paddr_to_vaddr` maps `paddr` writably for as long as the table lives,
///   preserves table-page alignment, and inverts `vaddr_to_paddr`.
///   Addresses passed to it are always clean.
///   If `fixed_mapping_offset` returns a value, wrapping addition of that value
///   must map every allocated table page to the same address as `paddr_to_vaddr`.
///   On architectures using BBM, access mappings must remain usable while an
///   affected old huge leaf is temporarily invalid.
/// * `allocate_table_page` returns a unique, page-aligned frame with a clean
///   address that `paddr_to_vaddr` can map. Its contents may be uninitialized;
///   the paging layer initializes it before use.
/// * `deallocate_table_page` is given only a currently live, exclusively owned
///   allocation returned by this allocator or one of its clones. It has not
///   previously been deallocated, no table links to it, and no software or
///   hardware access to it remains outstanding.
pub unsafe trait PagingAllocator: Clone + 'static {
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr;

    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr;

    fn fixed_mapping_offset(&self) -> Option<usize> {
        None
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError>;

    /// # Safety
    ///
    /// `paddr` must identify a currently live allocation returned by
    /// [`Self::allocate_table_page`] on this allocator or one of its clones.
    /// The caller must own it exclusively; it must not have been deallocated
    /// before, no table may link to it, and no software or hardware access to
    /// it may remain outstanding.
    unsafe fn deallocate_table_page(&self, paddr: PhysAddr);
}

/// An allocator whose memory is reachable at a fixed offset from its physical
/// address, which is what a kernel's direct map gives. Implementing it is
/// enough to be a [`PagingAllocator`].
///
/// # Safety
///
/// The obligations of [`PagingAllocator`] carry over, and `direct_map` must
/// report the region `allocate_table_page` draws from: a table built over the
/// region can then reach every page it is given.
pub unsafe trait DirectMappedAllocator: Clone + 'static {
    /// The physical region the allocator allocates from and maps as one piece.
    fn direct_map(&self) -> Range<PhysAddr>;

    /// Where the first address of [`Self::direct_map`] is reachable.
    fn direct_map_base(&self) -> VirtAddr;

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError>;

    /// # Safety
    ///
    /// `paddr` must identify a currently live allocation returned by
    /// [`Self::allocate_table_page`] on this allocator or one of its clones.
    /// The caller must own it exclusively; it must not have been deallocated
    /// before, no table may link to it, and no software or hardware access to
    /// it may remain outstanding.
    unsafe fn deallocate_table_page(&self, paddr: PhysAddr);
}

// SAFETY: the offset is fixed, so the two translations invert each other, and
// the rest is deferred to an implementation that owes the same obligations.
unsafe impl<T: DirectMappedAllocator> PagingAllocator for T {
    #[inline(always)]
    fn paddr_to_vaddr(&self, paddr: PhysAddr) -> VirtAddr {
        let offset = paddr.bits() - self.direct_map().start.bits();
        self.direct_map_base() + offset
    }

    #[inline(always)]
    fn vaddr_to_paddr(&self, vaddr: VirtAddr) -> PhysAddr {
        let offset = vaddr.bits() - self.direct_map_base().bits();
        self.direct_map().start + offset
    }

    #[inline(always)]
    fn fixed_mapping_offset(&self) -> Option<usize> {
        Some(self.direct_map_base().bits().wrapping_sub(self.direct_map().start.bits()))
    }

    fn allocate_table_page(&self) -> Result<PhysAddr, PagingError> {
        <T as DirectMappedAllocator>::allocate_table_page(self)
    }

    unsafe fn deallocate_table_page(&self, paddr: PhysAddr) {
        // SAFETY: the caller's obligation is the same in both traits.
        unsafe { <T as DirectMappedAllocator>::deallocate_table_page(self, paddr) }
    }
}
