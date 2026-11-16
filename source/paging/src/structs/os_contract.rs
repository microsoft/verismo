//! What an embedder owes the page table: allocation, the direct map, and TLB
//! invalidation. The page table allocates no memory and knows no virtual memory
//! layout of its own.
use core::ops::Range;
use core::sync::atomic::AtomicUsize;

use crate::structs::address::{Address, PhysAddr, VirtAddr};
use crate::structs::level::PageLevel;
use crate::structs::sizes::{PageSize, Regular};

/// Why an operation could not be carried out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PagingError {
    /// No frame was available for an intermediate table.
    AllocFrame,
    /// The walk found no mapping for the address.
    NotMapped,
    /// A mapping is already installed where one was asked for, at `level`.
    EntryAlreadyPresent { level: PageLevel },
    /// The requested page-table level is unsupported or mismatched.
    InvalidLevel,
    /// An address has invalid alignment or encoding for the operation.
    InvalidAddress,
    /// A range is reversed or not aligned to the smallest page size.
    InvalidRange,
    /// Requested mapping or root-register flags are invalid for the operation.
    InvalidFlags,
    /// This controller may not mutate the requested kernel mappings.
    PermissionDenied,
    /// The tree does not map one of its own table pages at the address the
    /// allocator hands out for that page.
    TablePageNotSelfMapped,
    /// A table pointer sits where a mapping was expected. Overwriting one would
    /// strand the subtree below it, so no operation on a leaf will.
    NotLeafEntry,
    /// A leaf exists, but its page size does not match the requested operation.
    WrongPageSize,
}

/// A failed range mapping and the number of input-size pages not inserted.
///
/// Pages preceding the remaining suffix stay mapped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MapRegionError {
    /// Why insertion stopped.
    pub error: PagingError,
    /// The failed page and unattempted suffix, measured in the input page size.
    pub unmapped_pages: usize,
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
///   `allocate_zeroed_table_page` has the same obligations and additionally
///   guarantees that every byte is zero.
/// * `deallocate_table_page` is given only a currently live, exclusively owned
///   allocation returned by this allocator provider. It has not
///   previously been deallocated, no table links to it, and no software or
///   hardware access to it remains outstanding.
pub unsafe trait PagingAllocator: 'static {
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr;

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr;

    fn allocate_table_page() -> Result<PhysAddr, PagingError>;

    /// Allocates a page whose complete contents are zero.
    fn allocate_zeroed_table_page() -> Result<PhysAddr, PagingError> {
        let paddr = Self::allocate_table_page()?;
        let page = Self::paddr_to_vaddr(paddr).as_mut_ptr::<u8>();
        // SAFETY: successful allocation returns a unique, writable table page.
        unsafe { page.write_bytes(0, Regular::SIZE) };
        Ok(paddr)
    }

    /// # Safety
    ///
    /// `paddr` must identify a currently live allocation returned by
    /// [`Self::allocate_table_page`] on this allocator provider.
    /// The caller must own it exclusively; it must not have been deallocated
    /// before, no table may link to it, and no software or hardware access to
    /// it may remain outstanding.
    unsafe fn deallocate_table_page(paddr: PhysAddr);

    /// Process-wide share counter for the table page at `paddr`.
    ///
    /// [`crate::pagetable::PageTable::new_from_sharing_top`] and
    /// [`crate::pagetable::PageTable::populate_shared`] increment this when
    /// they borrow a root-level entry; [`crate::pagetable::PageTable::free_page_table_by_addr`]
    /// and [`crate::pagetable::PageTable::cleanup_page_tables_by_range`]
    /// consult it before freeing a root-level table page, refusing to free
    /// one that is still shared.
    ///
    /// Defaults to a single aggregate counter, initially zero. This can
    /// conservatively prevent reclamation of unrelated table pages while
    /// any tracked share exists; override it for per-page reclamation.
    /// Whether this is ever
    /// consulted or overridden is governed by the source table's own policy
    /// (see [`crate::structs::policy::PagingOwnershipPolicy::MAY_FREE_PAGE_TABLE_PAGES`]),
    /// not by anything on this trait: a policy that declares it never frees
    /// its shared top-level pages while sharing skips this tracking
    /// entirely, so `share_count` need not be overridden in that case.
    fn share_count(_paddr: PhysAddr) -> &'static AtomicUsize {
        static NONE_SHARED: AtomicUsize = AtomicUsize::new(0);
        &NONE_SHARED
    }
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

    /// Allocates a page whose complete contents are zero.
    fn allocate_zeroed_table_page() -> Result<PhysAddr, PagingError> {
        let paddr = Self::allocate_table_page()?;
        let page = Self::resolve_paddr(paddr).as_mut_ptr::<u8>();
        // SAFETY: successful allocation returns a unique, writable table page.
        unsafe { page.write_bytes(0, Regular::SIZE) };
        Ok(paddr)
    }

    /// # Safety
    ///
    /// `paddr` must identify a currently live allocation returned by
    /// [`Self::allocate_table_page`] on this allocator provider.
    /// The caller must own it exclusively; it must not have been deallocated
    /// before, no table may link to it, and no software or hardware access to
    /// it may remain outstanding.
    unsafe fn deallocate_table_page(paddr: PhysAddr);

    /// See [`PagingAllocator::share_count`], which the blanket
    /// `PagingAllocator` impl for `T: DirectMappedAllocator` forwards to
    /// this: override it here, not on `PagingAllocator` directly, since a
    /// type implementing only [`DirectMappedAllocator`] never implements
    /// `PagingAllocator` by hand.
    fn share_count(_paddr: PhysAddr) -> &'static AtomicUsize {
        static NONE_SHARED: AtomicUsize = AtomicUsize::new(0);
        &NONE_SHARED
    }
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

    fn allocate_zeroed_table_page() -> Result<PhysAddr, PagingError> {
        T::allocate_zeroed_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: the caller's obligation is the same in both traits.
        unsafe { T::deallocate_table_page(paddr) }
    }

    fn share_count(paddr: PhysAddr) -> &'static AtomicUsize {
        T::share_count(paddr)
    }
}
