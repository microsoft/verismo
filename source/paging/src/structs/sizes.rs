// SPDX-License-Identifier: MIT OR Apache-2.0

//! Page sizes and the address geometry of page-table levels.

use crate::structs::address::{Address, VirtAddr};
use crate::structs::level::PageLevel;

/// Marker type describing the width of the in-page byte offset, i.e. the page
/// shift. Every architecture modelled here has a 4 KiB smallest page, so the
/// shift is at least 12.
pub trait PageOffset {
    const SHIFT: usize;
}

/// Marker type describing the size of a page, following the `x86_64` crate's
/// `PageSize` trait.
pub trait PageSize: PageOffset {
    const SIZE: usize;
}

impl<T: PageOffset> PageSize for T {
    const SIZE: usize = 1usize << T::SHIFT;
}

/// Marker for a 4 KiB page.
pub struct Size4KiB;

/// Marker for a 2 MiB page.
pub struct Size2MiB;

/// Marker for a 1 GiB page.
pub struct Size1GiB;

impl PageOffset for Size4KiB {
    const SHIFT: usize = 12;
}

impl PageOffset for Size2MiB {
    const SHIFT: usize = 21;
}

impl PageOffset for Size1GiB {
    const SHIFT: usize = 30;
}

/// The smallest page this build maps, selected by `--cfg target_min_page=...`
/// alongside the target in `.cargo/config.toml`. Deliberately not a cargo
/// feature: features are additive, so any crate in the graph could enlarge the
/// page for everyone. There is no default.
#[cfg(target_min_page = "4kib")]
pub type MinPageSize = Size4KiB;

#[cfg(target_min_page = "2mib")]
/// The configured 2 MiB minimum page type.
pub type MinPageSize = Size2MiB;

#[cfg(target_min_page = "1gib")]
/// The configured 1 GiB minimum page type.
pub type MinPageSize = Size1GiB;

#[cfg(not(any(target_min_page = "4kib", target_min_page = "2mib", target_min_page = "1gib")))]
compile_error!(
    "no target_min_page: set --cfg target_min_page=\"4kib\"|\"2mib\"|\"1gib\" in .cargo/config.toml"
);

#[cfg(any(
    all(target_min_page = "4kib", any(target_min_page = "2mib", target_min_page = "1gib")),
    all(target_min_page = "2mib", target_min_page = "1gib")
))]
compile_error!("target_min_page was given more than one value");

/// Width of the in-page byte offset, in bits.
pub const PAGE_OFFSET_WIDTH: usize = MinPageSize::SHIFT;

/// Bytes in the smallest page.
pub const PAGE_SIZE: usize = 1usize << PAGE_OFFSET_WIDTH;

/// Bytes a table-page entry occupies, as a shift: an entry is one machine word.
#[cfg(target_pointer_width = "64")]
pub const ENTRY_WIDTH: usize = 3;

#[cfg(target_pointer_width = "32")]
pub const ENTRY_WIDTH: usize = 2;

/// How many entries a table page holds: one page, filled with entries.
pub const ENTRY_COUNT: usize = PAGE_SIZE >> ENTRY_WIDTH;

/// How many address bits one paging level indexes. Derived from the page size
/// rather than asked of each architecture, which could then disagree with
/// [`ENTRY_COUNT`].
pub const PAGE_TABLE_INDEX_WIDTH: usize = PAGE_OFFSET_WIDTH - ENTRY_WIDTH;

/// The low bits of a table index. Written by shifting in ones because `-` binds
/// tighter than `<<` in Rust, which makes the `(1 << W) - 1` form easy to get
/// wrong.
pub const INDEX_MASK: usize = !(usize::MAX << PAGE_TABLE_INDEX_WIDTH);

/// How far to shift an address to reach the index bits of `level`.
#[inline(always)]
pub const fn shift_at(level: PageLevel) -> usize {
    PAGE_OFFSET_WIDTH + level.depth() * PAGE_TABLE_INDEX_WIDTH
}

/// How much address space one entry at `level` covers.
#[inline(always)]
pub const fn level_size(level: PageLevel) -> usize {
    1usize << shift_at(level)
}

#[inline(always)]
pub const fn entry_index_bits(vaddr: usize, level: PageLevel) -> usize {
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

#[inline(always)]
pub fn entry_index(vaddr: VirtAddr, level: PageLevel) -> usize {
    entry_index_bits(vaddr.bits(), level)
}

pub fn entry_index_at<const L: usize>(vaddr: VirtAddr) -> usize {
    pt_entry_index_bits::<L>(vaddr.bits())
}

pub(crate) fn next_boundary(vaddr: VirtAddr, level: PageLevel, end: VirtAddr) -> VirtAddr {
    let base = vaddr.bits() & !(level.size() - 1);
    VirtAddr::from(base.saturating_add(level.size()).min(end.bits()))
}
