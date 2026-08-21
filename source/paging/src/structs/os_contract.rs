/// OS-level page table services: address translation and frame management.
///
/// Bridges the generic page table code to the OS memory allocator and
/// virtual-address layout. Every method is an associated function (no
/// `&self`) — the implementing type is used as a zero-sized marker and
/// never instantiated.
///
/// # Safety
///
/// Implementers must guarantee:
///
/// * **`paddr_to_vaddr`** — the returned virtual address is a valid,
///   dereferenceable mapping of `paddr` for the lifetime of the page table.
///   `paddr` is always a *clean* physical address (no encryption bits).
///
/// * **`allocate_physical_page`** — every successful call returns a *unique*,
///   page-aligned, *zeroed* physical frame whose address is *clean* (no
///   encryption/confidentiality bits). The frame remains valid until a
///   matching `deallocate_physical_page` call.
///
/// * **`deallocate_physical_page`** — `paddr` is a value previously returned by
///   `allocate_physical_page` that has not yet been freed.
///
/// # Cross-method invariant
///
/// `paddr_to_vaddr` must return a valid, writable mapping for every
/// address returned by `allocate_physical_page`. The generic page table code
/// calls `allocate_physical_page` and immediately passes the result to
/// `paddr_to_vaddr` in order to zero-initialise and populate newly
/// allocated page table pages. This invariant can be satisfied either
/// by a linear map of all physical memory (so `paddr_to_vaddr` works
/// for any physical address) or by having `allocate_physical_page` return only
/// frames that are already mapped.
pub unsafe trait PagingHandler: 'static + FromBytes {
    /// Translate a clean physical address to a virtual address suitable for
    /// accessing page table pages.
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr;

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr;

    /// Allocate a zeroed page-table frame.
    ///
    /// Returns the *clean* physical address of the frame — no encryption
    /// or confidentiality bits are set. Callers apply
    /// [`ArchPagingMeta::make_private_address`] when storing the address
    /// in a PTE.
    fn allocate_physical_page() -> Result<PhysAddr, PagingError>;

    /// Deallocate a page-table frame previously returned by
    /// [`allocate_physical_page`](Self::allocate_physical_page).
    ///
    /// # Safety
    ///
    /// `paddr` must be a clean physical address previously returned by
    /// `allocate_physical_page` and not yet freed.
    unsafe fn deallocate_physical_page(paddr: PhysAddr);
}