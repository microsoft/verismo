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

/// Stateless OS-level page-table services backed by global allocator state.
///
/// # Safety
///
/// * `paddr_to_vaddr` maps `paddr` writably for as long as the table lives,
///   preserves table-page alignment, and inverts `vaddr_to_paddr`.
///   Addresses passed to it are always clean.
///   On architectures using BBM, access mappings must remain usable while an
///   affected old huge leaf is temporarily invalid.
/// * `allocate_table_page` returns a unique, page-aligned frame with a clean
///   address that `paddr_to_vaddr` can map. Its contents may be uninitialized;
///   the paging layer initializes it before use.
/// * `deallocate_table_page` is given only a currently live, exclusively owned
///   allocation returned by this allocator provider. It has not
///   previously been deallocated, no table links to it, and no software or
///   hardware access to it remains outstanding.
pub unsafe trait PagingAllocator: 'static {
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr;

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr;

    fn allocate_table_page() -> Result<PhysAddr, PagingError>;

    /// # Safety
    ///
    /// `paddr` must identify a currently live allocation returned by
    /// [`Self::allocate_table_page`] on this allocator provider.
    /// The caller must own it exclusively; it must not have been deallocated
    /// before, no table may link to it, and no software or hardware access to
    /// it may remain outstanding.
    unsafe fn deallocate_table_page(paddr: PhysAddr);
}

/// An allocator whose memory is reachable at a fixed offset from its physical
/// address, which is what a kernel's direct map gives. Implementing it is
/// enough to be a [`PagingAllocator`].
///
/// # Safety
///
/// The obligations of [`PagingAllocator`] carry over. `direct_map` must report
/// the region `allocate_table_page` draws from and the virtual address where
/// that region begins: a table built over it can then reach every page it is
/// given.
pub unsafe trait DirectMappedAllocator: 'static {
    /// The physical allocation region and the virtual address of its first byte.
    fn direct_map() -> (Range<PhysAddr>, VirtAddr);

    /// A provider hook so monomorphization can erase conversion work for identity maps.
    #[inline(always)]
    fn resolve_paddr(paddr: PhysAddr) -> VirtAddr {
        let (physical, virtual_base) = Self::direct_map();
        virtual_base + (paddr.bits() - physical.start.bits())
    }

    /// The inverse provider hook, avoiding generic direct-map arithmetic when unnecessary.
    #[inline(always)]
    fn resolve_vaddr(vaddr: VirtAddr) -> PhysAddr {
        let (physical, virtual_base) = Self::direct_map();
        physical.start + (vaddr.bits() - virtual_base.bits())
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError>;

    /// # Safety
    ///
    /// `paddr` must identify a currently live allocation returned by
    /// [`Self::allocate_table_page`] on this allocator provider.
    /// The caller must own it exclusively; it must not have been deallocated
    /// before, no table may link to it, and no software or hardware access to
    /// it may remain outstanding.
    unsafe fn deallocate_table_page(paddr: PhysAddr);
}

// SAFETY: the offset is fixed, so the two translations invert each other, and
// the rest is deferred to an implementation that owes the same obligations.
unsafe impl<T: DirectMappedAllocator> PagingAllocator for T {
    #[inline(always)]
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
        T::resolve_paddr(paddr)
    }

    #[inline(always)]
    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
        T::resolve_vaddr(vaddr)
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        T::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: the caller's obligation is the same in both traits.
        unsafe { T::deallocate_table_page(paddr) }
    }
}
