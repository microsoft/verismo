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
    /// How many levels lie below this one. The leaf level is 0.
    pub open spec fn spec_depth(self) -> nat {
        match self {
            PageLevel::Level0 => 0nat,
            PageLevel::Level1 => 1nat,
            PageLevel::Level2 => 2nat,
            PageLevel::Level3 => 3nat,
            PageLevel::Level4 => 4nat,
        }
    }

    /// The level one step down, or `None` at the leaf, where a walk must stop.
    ///
    /// Refusing to descend past level 0 is not a convenience: at the leaf the
    /// hardware reads bit 7 as PAT rather than PS, so an entry that looks like
    /// a table pointer there is a mapping.
    pub open spec fn spec_child(self) -> Option<PageLevel> {
        match self {
            PageLevel::Level0 => None,
            PageLevel::Level1 => Some(PageLevel::Level0),
            PageLevel::Level2 => Some(PageLevel::Level1),
            PageLevel::Level3 => Some(PageLevel::Level2),
            PageLevel::Level4 => Some(PageLevel::Level3),
        }
    }

    pub open spec fn spec_is_leaf(self) -> bool {
        self is Level0
    }

    /// The level with `depth` levels below it, for the levels x86 has.
    pub open spec fn spec_from_depth(depth: nat) -> PageLevel {
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
            PageLevel::spec_from_depth(level.spec_depth()) == level,
            level.spec_depth() <= 4,
    {
    }

    /// A child is exactly one level shallower, which is what makes a walk
    /// terminate.
    pub proof fn lemma_child_decreases(level: PageLevel)
        requires
            level.spec_child() is Some,
        ensures
            level.spec_child().unwrap().spec_depth() == level.spec_depth() - 1,
    {
    }
}

} // verus!
#[verus_verify]
impl PageLevel {
    #[verus_spec(ret =>
        returns self.spec_depth() as usize
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

    #[verus_spec(ret =>
        returns self.spec_child()
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

    #[verus_spec(ret =>
        returns self.spec_is_leaf()
    )]
    pub fn is_leaf(&self) -> bool {
        matches!(self, PageLevel::Level0)
    }
}
