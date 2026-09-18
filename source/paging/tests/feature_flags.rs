//! Platform feature masks apply to requested flags, not inherited mappings.

mod common;

use std::sync::Arc;

#[cfg(feature = "concurrent")]
use common::WholeTreeLock;
use common::{load_entry, Allocator, Arena, ARENA};
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::level::{Lvl, PageLevel};
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
use paging::os_contract::PagingError;
use paging::pagetable::PageTable;
use paging::sizes::entry_index;
use paging::tlb::{MayNeedFlush, TlbFlush};
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Platform<const GLOBAL: bool>;

unsafe impl<const GLOBAL: bool> X86PagingParams for Platform<GLOBAL> {
    fn private_mask() -> usize {
        1 << 51
    }

    fn shared_mask() -> usize {
        1 << 50
    }

    fn supported_flags() -> PTEntryFlags {
        let optional = PTEntryFlags::all() & !(PTEntryFlags::PRESENT | PTEntryFlags::HUGE);
        if GLOBAL {
            optional
        } else {
            optional & !PTEntryFlags::GLOBAL
        }
    }

    fn flush_tlb_global_sync(_scope: FlushScope) {}
}

type Arch = X86Paging<Platform<false>>;
#[cfg(feature = "concurrent")]
type Table = PageTable<Arch, Allocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type Table = PageTable<Arch, Allocator, Lvl<3>>;

fn fixture() -> (Arc<Arena>, Table) {
    let arena = Arena::new(ARENA);
    #[cfg(feature = "concurrent")]
    let table = Table::new(WholeTreeLock::default(), PTEntryFlags::data()).unwrap();
    #[cfg(not(feature = "concurrent"))]
    let table = Table::new(PTEntryFlags::data()).unwrap();
    (arena, table)
}

unsafe fn adopt(root: PhysAddr) -> Result<Table, PagingError> {
    #[cfg(feature = "concurrent")]
    return unsafe { Table::from_root(WholeTreeLock::default(), root) };
    #[cfg(not(feature = "concurrent"))]
    unsafe {
        Table::from_root(root)
    }
}

fn discharge<T: TlbFlush>(pending: MayNeedFlush<T>) {
    // SAFETY: these test trees are never installed in hardware.
    unsafe { pending.ignore() };
}

unsafe fn assert_parent_flags(root: PhysAddr, addr: VirtAddr) {
    let mut page = root.bits();
    let mut level = PageLevel::Level3;
    for _ in 0..=PageLevel::Level3.depth() {
        let pte = (page as *const PTEntry<Arch>).wrapping_add(entry_index(addr, level));
        // SAFETY: the caller pins the inactive, host-backed tree.
        let entry = unsafe { load_entry(pte) };
        if !entry.is_table(level) {
            return;
        }
        assert!(!entry.flags().contains(PTEntryFlags::GLOBAL));
        page = entry.address();
        level = level.child().unwrap();
    }
    unreachable!("parent walk exceeded the tree depth")
}

macro_rules! feature_tests {
    ($module:ident, $fixture:path, $adopt:path) => {
        #[allow(unused_mut)]
        mod $module {
            use super::*;

            #[test]
            fn requested_flags_are_filtered_without_losing_attributes_or_address_tags() {
                let (arena, mut table) = $fixture();
                let direct = table.walk(VirtAddr::from(arena.base())).read();
                assert!(!direct.flags().contains(PTEntryFlags::GLOBAL));
                let addr = VirtAddr::from(0x4000_0000usize);
                let opaque = PTEntryFlags::from_bits_retain(1 << 10);
                let flags = PTEntryFlags::data()
                    | PTEntryFlags::HUGE
                    | PTEntryFlags::ACCESSED
                    | PTEntryFlags::DIRTY
                    | opaque;
                let parent = PTEntryFlags::PRESENT
                    | PTEntryFlags::WRITABLE
                    | PTEntryFlags::USER
                    | PTEntryFlags::GLOBAL;
                let frame = PhysAddr::from(arena.base());
                table
                    .map_with_parent_flags(
                        common::page_4k(addr),
                        common::frame_4k(frame),
                        flags,
                        false,
                        parent,
                    )
                    .unwrap();
                let mapped = table.walk(addr).read();
                // SAFETY: no other controller or hardware uses this tree.
                unsafe { assert_parent_flags(table.root_paddr(), addr) };
                assert!(!mapped.flags().contains(PTEntryFlags::GLOBAL));
                assert!(mapped.flags().contains(opaque | PTEntryFlags::HUGE));
                assert!(!mapped.is_shared());
                assert_eq!(mapped.leaf_address(PageLevel::Level0), frame);

                let flags = PTEntryFlags::PRESENT | PTEntryFlags::GLOBAL | opaque;
                discharge(set_flags_at!(table, addr, PageLevel::Level0, flags, true).unwrap());
                let protected = table.walk(addr).read();
                assert!(!protected
                    .flags()
                    .intersects(PTEntryFlags::GLOBAL | PTEntryFlags::WRITABLE));
                assert!(protected.flags().contains(
                    opaque | PTEntryFlags::HUGE | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY
                ));
                discharge(table.set_shared(common::page_4k(addr), true).unwrap());
                let shared = table.walk(addr).read();
                assert!(!shared.flags().contains(PTEntryFlags::GLOBAL));
                assert!(shared.flags().contains(
                    opaque | PTEntryFlags::HUGE | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY
                ));
                assert!(shared.is_shared());
                assert_eq!(shared.paddr_field() & (1 << 51), 0);
                assert_ne!(shared.paddr_field() & (1 << 50), 0);
                assert_eq!(table.phys_addr(addr), Ok(frame));

                let (result, pending) = table.set_flags_range(addr, addr + 4096, flags, true);
                result.unwrap();
                discharge(pending);
                assert!(!table.walk(addr).read().flags().contains(PTEntryFlags::GLOBAL));
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: every child belongs to this inactive, unaliased owner.
                unsafe { table.free_children() };
            }

            #[test]
            fn splitting_does_not_refilter_inherited_flags_in_unedited_neighbors() {
                let _arena = Arena::new(ARENA);
                #[cfg(feature = "concurrent")]
                let mut original =
                    PageTable::<X86Paging<Platform<true>>, Allocator, Lvl<3>, WholeTreeLock>::new(
                        WholeTreeLock::default(),
                        PTEntryFlags::data(),
                    )
                    .unwrap();
                #[cfg(not(feature = "concurrent"))]
                let mut original = PageTable::<X86Paging<Platform<true>>, Allocator, Lvl<3>>::new(
                    PTEntryFlags::data(),
                )
                .unwrap();
                let base = VirtAddr::from(0x4000_0000usize);
                original
                    .map(
                        common::page_2m(base),
                        common::frame_2m(PhysAddr::from(0x8000_0000usize)),
                        PTEntryFlags::data(),
                        false,
                    )
                    .unwrap();
                #[cfg(feature = "concurrent")]
                let (_locks, root) = original.leak();
                #[cfg(not(feature = "concurrent"))]
                let root = original.leak();
                // SAFETY: ownership transfers; only the requested-flag policy differs.
                let mut table = unsafe { $adopt(root) }.unwrap();
                let target = base + 7 * 4096;
                discharge(split_at!(table, target, PageLevel::Level0, true).unwrap());
                assert!(table.walk(target).read().flags().contains(PTEntryFlags::GLOBAL));
                discharge(
                    set_flags_at!(table, target, PageLevel::Level0, PTEntryFlags::data(), true)
                        .unwrap(),
                );
                assert!(!table.walk(target).read().flags().contains(PTEntryFlags::GLOBAL));
                assert!(table.walk(base).read().flags().contains(PTEntryFlags::GLOBAL));
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: the previous controller was consumed and no hardware uses the tree.
                unsafe { table.free_children() };
            }
        }
    };
}

feature_tests!(selected_controller, fixture, adopt);
