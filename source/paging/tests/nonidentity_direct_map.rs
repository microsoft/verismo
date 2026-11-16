//! Ensures nonidentity direct maps support construction, translation, and reclamation without assuming physical addresses are pointers.
mod common;

use common::{flags, Arena, Host, RebasedAllocator, ARENA};
use paging::{
    address::{PhysAddr, VirtAddr},
    arch::x86_64::X86_64Paging,
    pagetable::KernelPageTable,
    structs::Lvl,
};
use std::collections::BTreeSet;

type Table = KernelPageTable<X86_64Paging<Host>, RebasedAllocator, Lvl<3>>;

#[test]
fn nonidentity_direct_map_supports_construction_translation_and_drop() {
    let arena = Arena::new(ARENA);
    let physical_base = 0x2000_1000;
    arena.rebase(physical_base);
    let table = Table::new(flags()).unwrap();

    assert_eq!(table.root_paddr(), PhysAddr::from(physical_base));
    for offset in [0, 4096, ARENA / 2, ARENA - 4096] {
        let vaddr = VirtAddr::from(arena.base() + offset);
        assert_eq!(table.phys_addr(vaddr), Ok(PhysAddr::from(physical_base + offset)));
        assert_eq!(table.translate(vaddr).unwrap().size(), 4096);
    }

    let vaddr = VirtAddr::from(0x4000_0000usize);
    let frame = PhysAddr::from(0x6000_0000usize);
    table.map(common::page_4k(vaddr), common::frame_4k(frame), flags(), false).unwrap();
    assert_eq!(table.phys_addr(vaddr), Ok(frame));
    assert_eq!(table.translate(vaddr).unwrap().size(), 4096);
    assert_eq!(table.validate_page_table(), Ok(()));

    drop(table);
    let freed = arena.freed();
    assert_eq!(freed.len(), arena.allocated());
    assert_eq!(freed.iter().copied().collect::<BTreeSet<_>>().len(), freed.len());
}
