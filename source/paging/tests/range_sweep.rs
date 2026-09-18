//! Structural regression for hierarchical range protection.

mod common;

use std::sync::atomic::{AtomicUsize, Ordering};

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{flags, table, Allocator, Host};
use paging::address::{PhysAddr, VirtAddr};
use paging::level::Lvl;
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
use paging::os_contract::{DirectMappedAllocator, PagingAllocator, PagingError};
use paging::pagetable::PageTable;
use paging::{PTEntryFlags, X86Paging};

const PAGE: usize = 4096;
const PAGES: usize = 512;
const BASE: usize = 0x4000_0000;
const FRAME: usize = 0x4_0000_0000;

struct ResolutionCountingAllocator;
static RESOLUTIONS: AtomicUsize = AtomicUsize::new(0);

unsafe impl PagingAllocator for ResolutionCountingAllocator {
    fn paddr_to_vaddr(paddr: PhysAddr) -> VirtAddr {
        RESOLUTIONS.fetch_add(1, Ordering::Relaxed);
        Allocator::paddr_to_vaddr(paddr)
    }

    fn vaddr_to_paddr(vaddr: VirtAddr) -> PhysAddr {
        Allocator::vaddr_to_paddr(vaddr)
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        <Allocator as DirectMappedAllocator>::allocate_table_page()
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        // SAFETY: the wrapper preserves the allocator domain and ownership transfer.
        unsafe { <Allocator as DirectMappedAllocator>::deallocate_table_page(paddr) };
    }
}

#[cfg(feature = "concurrent")]
type CountingTable = PageTable<X86Paging<Host>, ResolutionCountingAllocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type CountingTable = PageTable<X86Paging<Host>, ResolutionCountingAllocator, Lvl<3>>;

fn readonly() -> PTEntryFlags {
    PTEntryFlags::PRESENT | PTEntryFlags::NX
}

#[test]
fn contiguous_4k_range_resolves_each_table_per_sweep_not_per_leaf() {
    let (_arena, table) = table();
    #[cfg(not(feature = "concurrent"))]
    let mut table = table;
    for page in 0..PAGES {
        table
            .map(
                common::page_4k(VirtAddr::from(BASE + page * PAGE)),
                common::frame_4k(PhysAddr::from(FRAME + page * PAGE)),
                flags(),
                false,
            )
            .unwrap();
    }

    #[cfg(feature = "concurrent")]
    let (locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let root = table.leak();
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let mut table = unsafe { CountingTable::from_root(root) }.unwrap();
    RESOLUTIONS.store(0, Ordering::Relaxed);

    let (result, pending) = table.set_flags_range(
        VirtAddr::from(BASE),
        VirtAddr::from(BASE + PAGES * PAGE),
        readonly(),
        true,
    );

    assert_eq!(result, Ok(()));
    // SAFETY: this host-backed tree is never installed in hardware.
    unsafe { pending.ignore() };
    let resolved = RESOLUTIONS.load(Ordering::Relaxed);
    assert!(resolved <= 12, "boundary probes and hierarchical sweep resolved {resolved} pages");
    assert!(!table.walk(VirtAddr::from(BASE)).read().writable());
    assert!(!table.walk(VirtAddr::from(BASE + (PAGES - 1) * PAGE)).read().writable());
}

#[test]
fn contiguous_4k_mapping_descends_once_per_covered_child_table() {
    let (_arena, table) = table();
    #[cfg(feature = "concurrent")]
    let (locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let root = table.leak();
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let mut table = unsafe { CountingTable::from_root(root) }.unwrap();

    let start = VirtAddr::from(BASE + PAGE);
    let end = VirtAddr::from(BASE + (PAGES + 1) * PAGE);
    RESOLUTIONS.store(0, Ordering::Relaxed);
    map_region_4k!(table, start, end, PhysAddr::from(FRAME + PAGE), flags()).unwrap();

    let resolved = RESOLUTIONS.load(Ordering::Relaxed);
    assert!(resolved <= 24, "hierarchical mapping resolved {resolved} table pages");
    assert_eq!(table.translate(start).unwrap().address(), PhysAddr::from(FRAME + PAGE));
    assert_eq!(
        table.translate(end - PAGE).unwrap().address(),
        PhysAddr::from(FRAME + PAGES * PAGE)
    );
}

#[test]
fn matching_4k_mapping_is_rejected_without_rewalking_the_range() {
    let (_arena, table) = table();
    #[cfg(not(feature = "concurrent"))]
    let mut table = table;
    let start = VirtAddr::from(BASE + PAGE);
    let end = VirtAddr::from(BASE + (PAGES + 1) * PAGE);
    map_region_4k!(table, start, end, PhysAddr::from(FRAME + PAGE), flags()).unwrap();

    #[cfg(feature = "concurrent")]
    let (locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let root = table.leak();
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let mut table = unsafe { CountingTable::from_root(root) }.unwrap();

    RESOLUTIONS.store(0, Ordering::Relaxed);
    assert!(matches!(
        map_region_4k!(table, start, end, PhysAddr::from(FRAME + PAGE), flags()),
        Err(failure) if matches!(failure.error, PagingError::EntryAlreadyPresent { .. })
    ));

    let resolved = RESOLUTIONS.load(Ordering::Relaxed);
    assert!(resolved <= 12, "collision check resolved {resolved} table pages");
}

#[test]
fn contiguous_4k_unmapping_descends_once_per_covered_child_table() {
    let (_arena, table) = table();
    #[cfg(not(feature = "concurrent"))]
    let mut table = table;
    let start = VirtAddr::from(BASE + PAGE);
    let end = VirtAddr::from(BASE + (PAGES + 1) * PAGE);
    map_region_4k!(table, start, end, PhysAddr::from(FRAME + PAGE), flags()).unwrap();

    #[cfg(feature = "concurrent")]
    let (locks, root) = table.leak();
    #[cfg(not(feature = "concurrent"))]
    let root = table.leak();
    #[cfg(feature = "concurrent")]
    // SAFETY: the wrapper preserves the allocator and lock domains of the leaked tree.
    let table = unsafe { CountingTable::from_root(locks, root) }.unwrap();
    #[cfg(not(feature = "concurrent"))]
    // SAFETY: the wrapper preserves the allocator domain of the leaked tree.
    let mut table = unsafe { CountingTable::from_root(root) }.unwrap();

    RESOLUTIONS.store(0, Ordering::Relaxed);
    let (all_mapped, pending) = table.unmap_region(start, end).unwrap();
    assert!(all_mapped);
    // SAFETY: this host-backed tree is never installed in hardware.
    unsafe { pending.ignore() };

    let resolved = RESOLUTIONS.load(Ordering::Relaxed);
    assert!(resolved <= 16, "hierarchical unmapping resolved {resolved} table pages");
    assert!(matches!(table.translate(start), Err(PagingError::NotMapped)));
    assert!(matches!(table.translate(end - PAGE), Err(PagingError::NotMapped)));
}
