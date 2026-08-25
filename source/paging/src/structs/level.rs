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
use builtin_macros::verus;
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

    /// How many levels lie below this one. The leaf level is 0.
    pub open spec fn spec_depth(&self) -> usize {
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
    pub open spec fn spec_child(&self) -> Option<PageLevel> {
        match self {
            PageLevel::Level0 => None,
            PageLevel::Level1 => Some(PageLevel::Level0),
            PageLevel::Level2 => Some(PageLevel::Level1),
            PageLevel::Level3 => Some(PageLevel::Level2),
            PageLevel::Level4 => Some(PageLevel::Level3),
        }
    }

    pub open spec fn spec_is_leaf(&self) -> bool {
        match self {
            PageLevel::Level0 => true,
            _ => false,
        }
    }

    /// How many levels lie below this one. The leaf level is 0.
    #[verifier::when_used_as_spec(spec_depth)]
    pub fn depth(&self) -> (ret: usize)
        returns
            self.spec_depth(),
    {
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
    #[verifier::when_used_as_spec(spec_child)]
    pub fn child(&self) -> (ret: Option<PageLevel>)
        returns
            self.spec_child(),
    {
        match self {
            PageLevel::Level0 => None,
            PageLevel::Level1 => Some(PageLevel::Level0),
            PageLevel::Level2 => Some(PageLevel::Level1),
            PageLevel::Level3 => Some(PageLevel::Level2),
            PageLevel::Level4 => Some(PageLevel::Level3),
        }
    }

    #[verifier::when_used_as_spec(spec_is_leaf)]
    pub fn is_leaf(&self) -> (ret: bool)
        returns
            self.spec_is_leaf(),
    {
        match self {
            PageLevel::Level0 => true,
            _ => false,
        }
    }

    /// Depth and level name each other, so a specification may use whichever
    /// reads better without the two drifting apart.
    pub proof fn lemma_depth_roundtrip(level: PageLevel)
        ensures
            PageLevel::from_nat(level.depth() as nat) == level,
            level.depth() <= 4,
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_from_nat_depth(depth: nat)
        requires
            depth <= 4,
        ensures
            PageLevel::from_nat(depth).depth() == depth,
    {
        if depth == 0 {
        } else if depth == 1 {
        } else if depth == 2 {
        } else if depth == 3 {
        } else {
            assert(depth == 4);
        }
    }

    pub proof fn lemma_parent_depth(level: PageLevel)
        requires
            level.depth() < 4,
        ensures
            (match level {
                PageLevel::Level0 => PageLevel::Level1,
                PageLevel::Level1 => PageLevel::Level2,
                PageLevel::Level2 => PageLevel::Level3,
                PageLevel::Level3 => PageLevel::Level4,
                PageLevel::Level4 => PageLevel::Level4,
            }).depth() == level.depth() as nat + 1,
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_from_nat_parent(level: PageLevel)
        requires
            level.depth() < 4,
        ensures
            PageLevel::from_nat(level.depth() as nat + 1) == match level {
                PageLevel::Level0 => PageLevel::Level1,
                PageLevel::Level1 => PageLevel::Level2,
                PageLevel::Level2 => PageLevel::Level3,
                PageLevel::Level3 => PageLevel::Level4,
                PageLevel::Level4 => PageLevel::Level4,
            },
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_eq_by_depth(a: PageLevel, b: PageLevel)
        requires
            a.depth() == b.depth(),
        ensures
            a == b,
    {
        match a {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
        match b {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_nonzero_not_leaf(level: PageLevel)
        requires
            level.depth() > 0,
        ensures
            !level.is_leaf(),
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_from_nat_child(level: PageLevel)
        requires
            level.depth() > 0,
        ensures
            PageLevel::from_nat((level.depth() as nat - 1) as nat).depth() + 1 == level.depth(),
            PageLevel::from_nat((level.depth() as nat - 1) as nat).depth() < level.depth(),
    {
        match level {
            PageLevel::Level0 => {},
            PageLevel::Level1 => {},
            PageLevel::Level2 => {},
            PageLevel::Level3 => {},
            PageLevel::Level4 => {},
        }
    }

    pub proof fn lemma_zero_depth_le(level: PageLevel)
        ensures
            PageLevel::from_nat(0).depth() <= level.depth(),
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
            level.child().unwrap().depth() == level.depth() as nat - 1,
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

