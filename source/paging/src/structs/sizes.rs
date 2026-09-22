// SPDX-License-Identifier: MIT OR Apache-2.0

//! Page sizes and the address geometry of page-table levels.

use crate::structs::address::{Address, VirtAddr};
use crate::structs::level::{LevelSpec, Lvl, PageLevel};

/// Marker type describing the width of the in-page byte offset.
pub trait PageOffset {
    const SHIFT: usize;
}

/// A page size tied to one statically known page-table level.
pub trait PageSize: PageOffset + LevelSpec {
    const SIZE: usize;
}

impl<T: PageOffset + LevelSpec> PageSize for T {
    const SIZE: usize = 1usize << T::SHIFT;
}

/// The smallest page this build maps, selected by `--cfg target_min_page=...`
/// alongside the target in `.cargo/config.toml`. Deliberately not a cargo
/// feature: features are additive, so any crate in the graph could enlarge the
/// page for everyone. There is no default.
#[cfg(target_min_page = "4kib")]
pub const PAGE_OFFSET_WIDTH: usize = 12;

#[cfg(target_min_page = "2mib")]
pub const PAGE_OFFSET_WIDTH: usize = 21;

#[cfg(target_min_page = "1gib")]
pub const PAGE_OFFSET_WIDTH: usize = 30;

#[cfg(not(any(target_min_page = "4kib", target_min_page = "2mib", target_min_page = "1gib")))]
compile_error!(
    "no target_min_page: set --cfg target_min_page=\"4kib\"|\"2mib\"|\"1gib\" in .cargo/config.toml"
);

#[cfg(any(
    all(target_min_page = "4kib", any(target_min_page = "2mib", target_min_page = "1gib")),
    all(target_min_page = "2mib", target_min_page = "1gib")
))]
compile_error!("target_min_page was given more than one value");

/// Bytes in the smallest page.
pub const PAGE_SIZE: usize = 1usize << PAGE_OFFSET_WIDTH;

/// Bytes a table-page entry occupies, as a shift: an entry is one machine word.
#[cfg(target_pointer_width = "64")]
pub const ENTRY_WIDTH: usize = 3;

#[cfg(target_pointer_width = "32")]
pub const ENTRY_WIDTH: usize = 2;

/// How many entries a table page holds: one page, filled with entries.
pub const PT_ENTRY_COUNT: usize = PAGE_SIZE >> ENTRY_WIDTH;

/// How many address bits one paging level indexes. Derived from the page size
/// rather than asked of each architecture, which could then disagree with
/// [`PT_ENTRY_COUNT`].
pub const PAGE_TABLE_INDEX_WIDTH: usize = PAGE_OFFSET_WIDTH - ENTRY_WIDTH;

impl<const L: usize> PageOffset for Lvl<L>
where
    Lvl<L>: LevelSpec,
{
    const SHIFT: usize = <Self as LevelSpec>::LEVEL.shift();
}

/// The regular leaf size at page-table level 0.
pub type Regular = Lvl<0>;

/// The huge leaf size at page-table level 1.
pub type Huge = Lvl<1>;

/// The address span represented by one level-2 entry.
pub type SizeLevel2 = Lvl<2>;

/// The address span represented by one level-3 entry.
pub type SizeLevel3 = Lvl<3>;

/// The address span represented by one level-4 entry.
pub type SizeLevel4 = Lvl<4>;

/// The low bits of a table index. Written by shifting in ones because `-` binds
/// tighter than `<<` in Rust, which makes the `(1 << W) - 1` form easy to get
/// wrong.
pub const INDEX_MASK: usize = !(usize::MAX << PAGE_TABLE_INDEX_WIDTH);

#[inline(always)]
pub const fn entry_index_bits(vaddr: usize, level: PageLevel) -> usize {
    (vaddr >> level.shift()) & INDEX_MASK
}

/// The entry `vaddr` selects at the level fixed by `L`, counted from the leaf.
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
