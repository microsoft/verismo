//! Which level of the tree a table page sits at.
//!
//! A level is a closed set rather than a `nat` because it indexes the two
//! things a walk must not get wrong: how far a page's entries are still allowed
//! to descend, and how many address bits an entry at that level maps. Leaf
//! entries are level 0, and the root of a 4-level tree is level 3.
//!
//! The level of a page is *ghost*: it is carried by the page's tracked tokens
//! (`PTPageSharedPerm`), not by its type. That is what lets one walk function
//! serve every level instead of a macro-generated family of them.
use builtin_macros::{verus, verus_spec, verus_verify};
use vstd::prelude::*;

verus! {

/// The level of a page-table page, counted from the leaf.
///
/// Level 0 holds the entries that map the architecture's smallest page; level
/// `n` holds entries that either map a page of `n` levels' worth of address
/// bits or point at a level `n - 1` page. x86 walks at most five levels, so
/// five variants cover every paging mode the architecture defines.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum PageLevel {
    Level0,
    Level1,
    Level2,
    Level3,
    Level4,
}

impl PageLevel {
    /// The level with `depth` levels below it, for the levels x86 has. Callers
    /// that model levels as `nat`s use this at the decoder boundary; the
    /// argument is counted from the leaf, so `from_nat(0)` is `Level0`, not the
    /// root.
    pub open spec fn from_nat(depth: nat) -> PageLevel {
        if depth == 0 {
            PageLevel::Level0
        } else if depth == 1 {
            PageLevel::Level1
        } else if depth == 2 {
            PageLevel::Level2
        } else if depth == 3 {
            PageLevel::Level3
        } else {
            PageLevel::Level4
        }
    }

    /// Depth and level name each other, so a specification may use whichever
    /// reads better without the two drifting apart.
    pub proof fn lemma_depth_roundtrip(level: PageLevel)
        ensures
            PageLevel::from_nat(level.depth() as nat) == level,
            level.depth() as nat <= 4,
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    /// A child is exactly one level shallower, which is what makes a walk
    /// terminate.
    pub proof fn lemma_child_decreases(level: PageLevel)
        requires
            level.child() is Some,
        ensures
            level.child().unwrap().depth() as nat == level.depth() as nat - 1,
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_no_child_is_leaf(level: PageLevel)
        ensures
            (level.child() is None) == level.is_leaf(),
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_leaf_cases(level: PageLevel)
        ensures
            level.is_leaf() == (level == PageLevel::Level0),
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }
}

} // verus!
verus! {

/// The level a page table is rooted at, as a type.
///
/// Only the root level is static. Every level *below* it is a value carried by
/// the walk, so this fixes how deep the tree is without generating a family of
/// per-level functions -- which is the whole reason the level of an interior
/// page is ghost state instead of a type parameter.
pub trait PagingLevel: 'static {
    const TOP_LEVEL: PageLevel;
}

pub struct PagingLevel4;

impl PagingLevel for PagingLevel4 {
    const TOP_LEVEL: PageLevel = PageLevel::Level4;
}

pub struct PagingLevel3;

impl PagingLevel for PagingLevel3 {
    const TOP_LEVEL: PageLevel = PageLevel::Level3;
}

pub struct PagingLevel2;

impl PagingLevel for PagingLevel2 {
    const TOP_LEVEL: PageLevel = PageLevel::Level2;
}

pub struct PagingLevel1;

impl PagingLevel for PagingLevel1 {
    const TOP_LEVEL: PageLevel = PageLevel::Level1;
}

} // verus!
#[verus_verify]
impl PageLevel {
    /// How many levels lie below this one. The leaf level is 0.
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        returns self.depth()
    )]
    pub fn depth(&self) -> usize {
        match self {
            PageLevel::Level0 => 0,
            PageLevel::Level1 => 1,
            PageLevel::Level2 => 2,
            PageLevel::Level3 => 3,
            PageLevel::Level4 => 4,
        }
    }

    /// The level one step down, or `None` at the leaf, where a walk must stop.
    ///
    /// Refusing to descend past level 0 is not a convenience: at the leaf the
    /// hardware reads bit 7 as PAT rather than PS, so an entry that looks like
    /// a table pointer there is a mapping.
    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        returns self.child()
    )]
    pub fn child(&self) -> Option<PageLevel> {
        match self {
            PageLevel::Level0 => None,
            PageLevel::Level1 => Some(PageLevel::Level0),
            PageLevel::Level2 => Some(PageLevel::Level1),
            PageLevel::Level3 => Some(PageLevel::Level2),
            PageLevel::Level4 => Some(PageLevel::Level3),
        }
    }

    #[verus_verify(dual_spec)]
    #[verus_spec(ret =>
        returns self.is_leaf()
    )]
    pub fn is_leaf(&self) -> bool {
        match self {
            PageLevel::Level0 => true,
            _ => false,
        }
    }
}
