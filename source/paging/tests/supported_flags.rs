//! Ensures supported flags filter new requests without corrupting inherited mappings or widening parent permissions.
mod common;

use common::{load_entry, Allocator, Arena, ARENA};
use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    pagetable::KernelPageTable,
    structs::{entry_index, Lvl, PTEntry, PageLevel},
    tlb::{MayNeedFlush, TlbFlush},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Platform<const GLOBAL: bool>;

unsafe impl<const GLOBAL: bool> X86_64PagingParams for Platform<GLOBAL> {
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

type Arch = X86_64Paging<Platform<false>>;
type Table = KernelPageTable<Arch, Allocator, Lvl<3>>;

fn discharge<T: TlbFlush>(pending: MayNeedFlush<T>) {
    // SAFETY: these test trees are never installed in hardware.
    unsafe { pending.ignore() };
}

unsafe fn ancestors(root: PhysAddr, addr: VirtAddr) -> Vec<PTEntry<Arch>> {
    let mut page = root.bits();
    let mut level = PageLevel::Level3;
    let mut parents = Vec::new();
    while let Some(child) = level.child() {
        let pte = (page as *const PTEntry<Arch>).wrapping_add(entry_index(addr, level));
        // SAFETY: the caller pins the inactive, host-backed tree.
        let entry = unsafe { load_entry(pte) };
        if !entry.is_present_table(level) {
            break;
        }
        parents.push(entry);
        page = entry.address();
        level = child;
    }
    parents
}

#[test]
fn requested_flags_are_filtered_without_losing_attributes_or_address_tags() {
    let arena = Arena::new(ARENA);
    let table = Table::new(PTEntryFlags::data()).unwrap();
    let direct = table.walk(VirtAddr::from(arena.base())).read();
    assert!(!direct.flags().contains(PTEntryFlags::GLOBAL));
    let addr = VirtAddr::from(0x4000_0000usize);
    let opaque = PTEntryFlags::from_bits_retain(1 << 10);
    let flags = PTEntryFlags::data()
        | PTEntryFlags::HUGE
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY
        | opaque;
    let parent =
        PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER | PTEntryFlags::GLOBAL;
    let frame = PhysAddr::from(arena.base());
    let page = common::page_4k(addr);
    table.map_with_parent_flags(page, common::frame_4k(frame), flags, false, parent).unwrap();
    let mapped = table.walk(addr).read();
    // SAFETY: no other controller or hardware uses this tree.
    for parent in unsafe { ancestors(table.root_paddr(), addr) } {
        assert!(!parent.flags().contains(PTEntryFlags::GLOBAL));
    }
    assert!(!mapped.flags().contains(PTEntryFlags::GLOBAL));
    assert!(mapped.flags().contains(opaque | PTEntryFlags::HUGE));
    assert!(!mapped.is_shared());
    assert_eq!(mapped.leaf_address(PageLevel::Level0), frame);

    let flags = PTEntryFlags::PRESENT | PTEntryFlags::GLOBAL | opaque;
    discharge(table.set_flags(page, flags, true).unwrap());
    let protected = table.walk(addr).read();
    assert!(!protected.flags().intersects(PTEntryFlags::GLOBAL | PTEntryFlags::WRITABLE));
    assert!(protected
        .flags()
        .contains(opaque | PTEntryFlags::HUGE | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
    discharge(table.set_shared(page, true).unwrap());
    let shared = table.walk(addr).read();
    assert!(!shared.flags().contains(PTEntryFlags::GLOBAL));
    assert!(shared
        .flags()
        .contains(opaque | PTEntryFlags::HUGE | PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY));
    assert!(shared.is_shared());
    assert_eq!(shared.paddr_field() & (1 << 51), 0);
    assert_ne!(shared.paddr_field() & (1 << 50), 0);
    assert_eq!(table.phys_addr(addr), Ok(frame));

    let (result, pending) = table.set_flags_range(addr, addr + 4096, flags, true);
    result.unwrap();
    discharge(pending);
    assert!(!table.walk(addr).read().flags().contains(PTEntryFlags::GLOBAL));
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn splitting_does_not_refilter_inherited_flags_in_unedited_neighbors() {
    let _arena = Arena::new(ARENA);
    let original = KernelPageTable::<X86_64Paging<Platform<true>>, Allocator, Lvl<3>>::new(
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
    let root = original.leak();
    // SAFETY: ownership transfers; only the requested-flag policy differs.
    let table = unsafe { Table::from_root(root) }.unwrap();
    let target = base + 7 * 4096;
    discharge(table.split(common::page_2m(base), true).unwrap());
    assert!(table.walk(target).read().flags().contains(PTEntryFlags::GLOBAL));
    discharge(table.set_flags(common::page_4k(target), PTEntryFlags::data(), true).unwrap());
    assert!(!table.walk(target).read().flags().contains(PTEntryFlags::GLOBAL));
    assert!(table.walk(base).read().flags().contains(PTEntryFlags::GLOBAL));
    assert_eq!(table.validate_page_table(), Ok(()));
}

#[test]
fn mapping_and_protection_do_not_widen_restrictive_parents() {
    let arena = Arena::new(ARENA);
    let table = Table::new(PTEntryFlags::data()).unwrap();
    let addr = VirtAddr::from(0x4000_0000usize);
    let parent = PTEntryFlags::PRESENT
        | PTEntryFlags::NX
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY
        | PTEntryFlags::from_bits_retain(1 << 10);
    let frame = PhysAddr::from(arena.base());
    table
        .map_with_parent_flags(
            common::page_4k(addr),
            common::frame_4k(frame),
            PTEntryFlags::data(),
            false,
            parent,
        )
        .unwrap();
    // SAFETY: this inactive, host-backed tree remains owned throughout the test.
    let before = unsafe { ancestors(table.root_paddr(), addr) };
    assert_eq!(before.len(), 3);
    let allocated = arena.allocated();
    let writable = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::USER;
    table
        .map(common::page_4k(addr + 4096), common::frame_4k(frame + 4096), writable, false)
        .unwrap();
    discharge(table.set_flags(common::page_4k(addr), writable, true).unwrap());
    for offset in [0, 4096] {
        assert!(table.walk(addr + offset).read().flags().contains(writable));
        // SAFETY: the controller pins every ancestor and hardware never uses this root.
        let after = unsafe { ancestors(table.root_paddr(), addr + offset) };
        assert_eq!(before.len(), after.len());
        for (old, new) in before.iter().zip(after) {
            assert_eq!(old.raw(), new.raw());
            assert!(new.flags().contains(parent));
            assert!(!new.flags().intersects(PTEntryFlags::WRITABLE | PTEntryFlags::USER));
        }
    }
    assert_eq!(arena.allocated(), allocated);
    assert_eq!(table.validate_page_table(), Ok(()));
}
