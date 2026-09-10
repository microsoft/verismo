//! Turning an address into the slot a level's table page holds for it. The
//! level is a value, so the index arithmetic is ordinary arithmetic rather than
//! a family of constants generated per level.
use crate::structs::address::{Address, VirtAddr};
use crate::structs::level::PageLevel;
use crate::structs::sizes::{PAGE_OFFSET_WIDTH, PAGE_TABLE_INDEX_WIDTH};

/// The low bits of a table index. Written by shifting in ones because `-` binds
/// tighter than `<<` in Rust, which makes the `(1 << W) - 1` form easy to get
/// wrong.
pub const INDEX_MASK: usize = !(usize::MAX << PAGE_TABLE_INDEX_WIDTH);

/// How far to shift an address to reach the index bits of `level`.
pub fn shift_at(level: PageLevel) -> usize {
    PAGE_OFFSET_WIDTH + level.depth() * PAGE_TABLE_INDEX_WIDTH
}

/// How much address space one entry at `level` covers.
pub fn level_size(level: PageLevel) -> usize {
    1usize << shift_at(level)
}

pub fn entry_index_bits(vaddr: usize, level: PageLevel) -> usize {
    (vaddr >> shift_at(level)) & INDEX_MASK
}

/// The entry `vaddr` selects at the level fixed by `L`, counted from the leaf.
/// Deliberately not `VirtAddr::to_pgtbl_idx`, which spells out x86-64's shift
/// and mask; the geometry here comes from the page size instead.
pub const fn pt_entry_index_bits<const L: usize>(vaddr: usize) -> usize {
    // `let`, not an inner `const` item: that cannot name the outer `L` (E0401),
    // and `L` is fixed at monomorphization anyway.
    let shift = PAGE_OFFSET_WIDTH + L * PAGE_TABLE_INDEX_WIDTH;
    (vaddr >> shift) & INDEX_MASK
}

pub fn entry_index(vaddr: VirtAddr, level: PageLevel) -> usize {
    entry_index_bits(vaddr.bits(), level)
}

pub fn entry_index_at<const L: usize>(vaddr: VirtAddr) -> usize {
    pt_entry_index_bits::<L>(vaddr.bits())
}
