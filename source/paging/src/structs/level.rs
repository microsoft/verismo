use vstd::prelude::*;

use crate::structs::arch_contract::{level_shift, ArchPagingGeometry};
use crate::structs::sizes::{PageOffset, PageSize, Size1GiB, Size2MiB, Size4KiB};

verus! {

/// Runtime paging-tree depth, for code that dispatches on a depth it learns
/// dynamically (e.g. by walking hardware tables). Depths count up from the
/// leaf: depth 0 maps `A::MinPageSize`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(usize)]
pub enum PageLevel {
    Level0 = 0,
    Level1 = 1,
    Level2 = 2,
    Level3 = 3,
    Level4 = 4,
}

impl PageLevel {
    pub open spec fn depth(self) -> nat {
        self as int as nat
    }
}

/// A compile-time paging-level marker. Implementors are zero-sized types that
/// let level-indexed code (entries, tables, walks) be generic over depth
/// while keeping depth arithmetic in the type system. `LEVEL` is the runtime
/// counterpart of `DEPTH`; `lemma_depth_matches_level` is the obligation an
/// implementor owes to keep the two representations in sync.
pub trait PagingLevel: 'static {
    /// Distance from the leaf level, e.g. 0 for the level mapping
    /// `A::MinPageSize`.
    const DEPTH: usize;

    const LEVEL: PageLevel;

    proof fn lemma_depth_matches_level()
        ensures
            Self::LEVEL.depth() == Self::DEPTH as nat,
    ;
}

/// A level with a level below it, i.e. not the leaf. Implementors own the
/// obligation that `Lower` is exactly one depth closer to the leaf.
pub trait InteriorLevel: PagingLevel {
    type Lower: PagingLevel;

    proof fn lemma_lower_depth()
        ensures
            Self::Lower::DEPTH + 1 == Self::DEPTH,
    ;
}

/// A level whose entries map pages directly, rather than pointing at a lower
/// table. `Size` is the page size mapped at this level.
///
/// This trait deliberately says nothing about how `Size::SHIFT` relates to
/// the architecture's level geometry: that agreement only holds for
/// architectures whose `level_index_width()` matches the marker's spacing
/// (9 bits, for the `Level0`/`Level1`/`Level2` markers below), and is left
/// for `maps_page_shift_agrees_with_geometry` to state and each architecture
/// to discharge.
pub trait MapsPage: PagingLevel {
    type Size: PageSize;
}

/// Whether `L`'s mapped page size shift matches the shift `A`'s geometry
/// assigns to `L`'s depth. Not proved here: it only holds once
/// `A::level_index_width()` is fixed to match how `L::Size` was chosen (9,
/// for `Level0`/`Level1`/`Level2`). Architectures instantiate and discharge
/// this themselves.
pub open spec fn maps_page_shift_agrees_with_geometry<
    A: ArchPagingGeometry,
    L: MapsPage,
>() -> bool {
    <L::Size as PageOffset>::SHIFT as nat == level_shift::<A>(L::DEPTH as nat)
}

pub struct Level0;

pub struct Level1;

pub struct Level2;

pub struct Level3;

pub struct Level4;

impl PagingLevel for Level0 {
    const DEPTH: usize = 0;

    const LEVEL: PageLevel = PageLevel::Level0;

    proof fn lemma_depth_matches_level() {
        assert(PageLevel::Level0 as int == 0) by (compute);
    }
}

impl PagingLevel for Level1 {
    const DEPTH: usize = 1;

    const LEVEL: PageLevel = PageLevel::Level1;

    proof fn lemma_depth_matches_level() {
        assert(PageLevel::Level1 as int == 1) by (compute);
    }
}

impl PagingLevel for Level2 {
    const DEPTH: usize = 2;

    const LEVEL: PageLevel = PageLevel::Level2;

    proof fn lemma_depth_matches_level() {
        assert(PageLevel::Level2 as int == 2) by (compute);
    }
}

impl PagingLevel for Level3 {
    const DEPTH: usize = 3;

    const LEVEL: PageLevel = PageLevel::Level3;

    proof fn lemma_depth_matches_level() {
        assert(PageLevel::Level3 as int == 3) by (compute);
    }
}

impl PagingLevel for Level4 {
    const DEPTH: usize = 4;

    const LEVEL: PageLevel = PageLevel::Level4;

    proof fn lemma_depth_matches_level() {
        assert(PageLevel::Level4 as int == 4) by (compute);
    }
}

impl InteriorLevel for Level1 {
    type Lower = Level0;

    proof fn lemma_lower_depth() {
    }
}

impl InteriorLevel for Level2 {
    type Lower = Level1;

    proof fn lemma_lower_depth() {
    }
}

impl InteriorLevel for Level3 {
    type Lower = Level2;

    proof fn lemma_lower_depth() {
    }
}

impl InteriorLevel for Level4 {
    type Lower = Level3;

    proof fn lemma_lower_depth() {
    }
}

impl MapsPage for Level0 {
    type Size = Size4KiB;
}

impl MapsPage for Level1 {
    type Size = Size2MiB;
}

impl MapsPage for Level2 {
    type Size = Size1GiB;
}

} // verus!
