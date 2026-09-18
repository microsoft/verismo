//! Parent permissions are established at creation, not changed by leaf edits.

mod common;

use std::sync::Arc;

use common::{load_entry, Allocator, Arena, Host};
#[cfg(feature = "concurrent")]
use common::{WholeTreeLock, ARENA};
use paging::address::{Address, PhysAddr, VirtAddr};
use paging::entry::PTEntry;
use paging::level::{Lvl, PageLevel};
#[cfg(not(feature = "concurrent"))]
use paging::mapping::MappingRefOps;
use paging::pagetable::PageTable;
use paging::sizes::entry_index;
use paging::tlb::{MayNeedFlush, TlbFlush};
use paging::{FlushScope, PTEntryFlags, X86Paging, X86TlbFlushTok};

type Arch = X86Paging<Host>;
#[cfg(feature = "concurrent")]
type Table = PageTable<Arch, Allocator, Lvl<3>, WholeTreeLock>;
#[cfg(not(feature = "concurrent"))]
type Table = PageTable<Arch, Allocator, Lvl<3>>;

fn fixture() -> (Arc<Arena>, Table) {
    #[cfg(not(feature = "concurrent"))]
    return common::table();
    #[cfg(feature = "concurrent")]
    let arena = Arena::new(ARENA);
    #[cfg(feature = "concurrent")]
    let table = Table::new(WholeTreeLock::default(), common::flags()).unwrap();
    #[cfg(feature = "concurrent")]
    (arena, table)
}

fn discharge<T: TlbFlush>(pending: MayNeedFlush<T>) {
    // SAFETY: these test trees are never installed.
    unsafe { pending.ignore() };
}

unsafe fn ancestors(root: PhysAddr, addr: VirtAddr) -> Vec<PTEntry<Arch>> {
    let mut page = root.bits();
    let mut level = PageLevel::Level3;
    let mut result = Vec::new();
    while let Some(child) = level.child() {
        let slot = (page as *const PTEntry<Arch>).wrapping_add(entry_index(addr, level));
        // SAFETY: the caller pins this host-backed tree; no entry references escape.
        let entry = unsafe { load_entry(slot) };
        if !entry.is_table(level) {
            break;
        }
        result.push(entry);
        page = entry.address();
        level = child;
    }
    result
}

macro_rules! parent_tests {
    ($module:ident, $fixture:path) => {
        mod $module {
            use super::*;

            #[test]
            fn default_parents_allow_later_writable_and_executable_leaves() {
                let (arena, mut table) = $fixture();
                let addr = VirtAddr::from(0x4000_0000usize);
                let frame = PhysAddr::from(arena.base());
                let readonly = PTEntryFlags::PRESENT | PTEntryFlags::USER | PTEntryFlags::NX;
                let writable = PTEntryFlags::PRESENT | PTEntryFlags::USER | PTEntryFlags::WRITABLE;
                table.map(common::page_4k(addr), common::frame_4k(frame), readonly, false).unwrap();
                // SAFETY: the inactive tree remains owned throughout these observations.
                let before = unsafe { ancestors(table.root_paddr(), addr) };
                for offset in [4096, 2 * 1024 * 1024] {
                    table
                        .map(
                            common::page_4k(addr + offset),
                            common::frame_4k(frame + 4096),
                            writable,
                            false,
                        )
                        .unwrap();
                    let leaf = table.walk(addr + offset).read();
                    assert!(leaf.flags().contains(writable));
                    assert!(!leaf.flags().contains(PTEntryFlags::NX));
                    for parent in unsafe { ancestors(table.root_paddr(), addr + offset) } {
                        assert!(parent.flags().contains(writable));
                        assert!(!parent.flags().contains(PTEntryFlags::NX));
                    }
                }
                discharge(set_flags_at!(table, addr, PageLevel::Level0, writable, true).unwrap());
                assert!(table.walk(addr).read().flags().contains(writable));
                assert!(!table.walk(addr).read().flags().contains(PTEntryFlags::NX));
                assert_eq!(table.phys_addr(addr), Ok(frame));
                let after = unsafe { ancestors(table.root_paddr(), addr) };
                assert_eq!(before.len(), 3);
                for (old, new) in before.iter().zip(after) {
                    assert_eq!(old.raw(), new.raw());
                    assert!(new.flags().contains(writable));
                    assert!(!new.flags().contains(PTEntryFlags::NX));
                }
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: all descendants belong to this inactive, unaliased tree.
                unsafe { table.free_children() };
            }

            #[test]
            fn new_parents_are_present_nonhuge_tables() {
                let (arena, mut table) = $fixture();
                let addr = VirtAddr::from(0xffff_8000_4000_0000usize);
                let frame = PhysAddr::from(arena.base());
                table
                    .map_with_parent_flags(
                        common::page_4k(addr),
                        common::frame_4k(frame),
                        common::flags(),
                        false,
                        PTEntryFlags::NX | PTEntryFlags::HUGE,
                    )
                    .unwrap();
                // SAFETY: the inactive tree remains exclusively owned.
                let parents = unsafe { ancestors(table.root_paddr(), addr) };
                assert_eq!(parents.len(), 3);
                for parent in parents {
                    assert!(parent.present());
                    assert!(!parent.huge());
                    assert!(parent.flags().contains(PTEntryFlags::NX));
                    assert!(!parent
                        .flags()
                        .intersects(PTEntryFlags::WRITABLE | PTEntryFlags::USER));
                }
                assert_eq!(table.phys_addr(addr), Ok(frame));
                // SAFETY: every descendant belongs to this inactive, unaliased tree.
                unsafe { table.free_children() };
            }

            #[test]
            fn mapping_and_protection_do_not_widen_existing_restrictive_parents() {
                let (arena, mut table) = $fixture();
                let addr = VirtAddr::from(0x4000_0000usize);
                let parent = PTEntryFlags::PRESENT
                    | PTEntryFlags::NX
                    | PTEntryFlags::ACCESSED
                    | PTEntryFlags::DIRTY
                    | PTEntryFlags::from_bits_retain(1 << 10);
                table
                    .map_with_parent_flags(
                        common::page_4k(addr),
                        common::frame_4k(PhysAddr::from(arena.base())),
                        common::flags(),
                        false,
                        parent,
                    )
                    .unwrap();
                // SAFETY: these host-backed tables are inactive and remain owned.
                let before = unsafe { ancestors(table.root_paddr(), addr) };
                let allocated = arena.allocated();
                let writable = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER;
                table
                    .map(
                        common::page_4k(addr + 4096),
                        common::frame_4k(PhysAddr::from(arena.base() + 4096)),
                        writable,
                        false,
                    )
                    .unwrap();
                discharge(set_flags_at!(table, addr, PageLevel::Level0, writable, true).unwrap());
                for offset in [0, 4096] {
                    assert!(table.walk(addr + offset).read().flags().contains(writable));
                    let after = unsafe { ancestors(table.root_paddr(), addr + offset) };
                    assert_eq!(before.len(), after.len());
                    for (old, new) in before.iter().zip(after) {
                        assert_eq!(old.raw(), new.raw());
                        assert!(new.flags().contains(parent));
                        assert!(!new
                            .flags()
                            .intersects(PTEntryFlags::WRITABLE | PTEntryFlags::USER));
                    }
                }
                assert_eq!(arena.allocated(), allocated);
                assert_eq!(table.validate_page_table(), Ok(()));
                // SAFETY: every table belongs to this inactive, unaliased owner.
                unsafe { table.free_children() };
            }
        }
    };
}

parent_tests!(selected_controller, fixture);

#[test]
fn flushes_crossing_the_canonical_gap_or_address_end_use_all() {
    for addr in [0x0000_7fff_ffff_f000usize, 0xffff_ffff_ffff_f000usize] {
        let pending =
            MayNeedFlush::<X86TlbFlushTok<Host>>::new(VirtAddr::from(addr), PageLevel::Level0);
        assert_eq!(pending.scope().as_ref().unwrap().scope(), FlushScope::All);
        discharge(pending);
    }
}
