// SPDX-License-Identifier: MIT OR Apache-2.0

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

pub struct Size4KiB;

pub struct Size2MiB;

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

impl<T: PageOffset> PageSize for T {
    const SIZE: usize = 1usize << T::SHIFT;
}

/// The smallest page this build maps, selected by `--cfg target_min_page=...`
/// alongside the target in `.cargo/config.toml`. Deliberately not a cargo
/// feature: features are additive, so any crate in the graph could enlarge the
/// page for everyone. There is no default.
#[cfg(target_min_page = "4kib")]
pub type MinPageSize = Size4KiB;

#[cfg(target_min_page = "2mib")]
pub type MinPageSize = Size2MiB;

#[cfg(target_min_page = "1gib")]
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
#[cfg(target_min_page = "4kib")]
pub const PAGE_OFFSET_WIDTH: usize = 12;

#[cfg(target_min_page = "2mib")]
pub const PAGE_OFFSET_WIDTH: usize = 21;

#[cfg(target_min_page = "1gib")]
pub const PAGE_OFFSET_WIDTH: usize = 30;

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
