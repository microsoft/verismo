//! Which level of the tree a table page sits at.
//!
//! A level is a closed set rather than a `nat` because it indexes the two
//! things a walk must not get wrong: how far a page's entries are still allowed
//! to descend, and how many address bits an entry at that level maps. Leaf
//! entries are level 0, and the root of a 4-level tree is level 3.
//!
//! The level of a page is *ghost*: it is carried by the page's tracked tokens
//! (`PTPageSharedPerm`), not by its type. `PageLevel` is that value form.
//! Alongside it, `Lvl<L>` names a level as a *type*, for code whose level is
//! fixed when the crate is compiled -- the unrolled walkers, and the root a
//! handle is generic over. `LevelSpec::level` is the bridge, so a
//! specification may be written against whichever form reads better.
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

    /// The level one step up, saturating at level 4. Below level 4 it is the
    /// inverse of `spec_child`.
    pub open spec fn spec_parent(&self) -> PageLevel {
        match self {
            PageLevel::Level0 => PageLevel::Level1,
            PageLevel::Level1 => PageLevel::Level2,
            PageLevel::Level2 => PageLevel::Level3,
            PageLevel::Level3 => PageLevel::Level4,
            PageLevel::Level4 => PageLevel::Level4,
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

    /// The level at depth `L`, named by a const parameter rather than passed as
    /// a value.
    ///
    /// This is what lets a caller whose level is fixed at compile time -- an
    /// unrolled walker, say -- carry the level in its type instead of in a
    /// local, without giving up the shared `from_nat` specification.
    pub const fn at<const L: usize>() -> (ret: PageLevel)
        requires
            L <= 4,
        ensures
            ret == PageLevel::from_nat(L as nat),
            ret.depth() == L,
    {
        let ret = match L {
            0 => PageLevel::Level0,
            1 => PageLevel::Level1,
            2 => PageLevel::Level2,
            3 => PageLevel::Level3,
            _ => PageLevel::Level4,
        };
        proof {
            PageLevel::lemma_from_nat_depth(L as nat);
        }
        ret
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
            level.spec_parent().depth() == level.depth() as nat + 1,
            level.spec_parent().spec_child() == Some(level),
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
            PageLevel::from_nat(level.depth() as nat + 1) == level.spec_parent(),
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

/// A level of the tree, as a type: `L` is the depth above the leaf, so `Lvl<0>`
/// is the leaf and `Lvl<4>` the root of a five-level tree.
///
/// The numbering matches `PageLevel::spec_depth` and the shift in
/// `geometry::shift_at`, both of which count from the leaf, so a marker's `L`
/// is directly the number of index widths its entries shift by.
///
/// Only levels the architecture defines get an impl of [`LevelSpec`]: `Lvl<7>`
/// is a type that names no level, and so cannot be used as one.
pub struct Lvl<const L: usize>;

/// What a level marker knows: its depth, and the same level as a value.
///
/// `LEVEL` is the bridge to [`PageLevel`], which stays the ghost and runtime
/// form. A specification may be written against either without the two drifting
/// apart, because `lemma_wf` ties them together.
pub trait LevelSpec: 'static {
    const DEPTH: usize;

    const LEVEL: PageLevel;

    proof fn lemma_wf()
        ensures
            Self::LEVEL.depth() == Self::DEPTH,
            Self::DEPTH <= 4,
    ;
}

/// A level with another level beneath it.
///
/// `Lvl<0>` has no impl, so descending below the leaf is a type error rather
/// than a runtime check -- at the leaf the hardware reads bit 7 as PAT rather
/// than PS, so an entry that looks there like a table pointer is a mapping.
pub trait InnerLevel: LevelSpec {
    type Child: LevelSpec;

    proof fn lemma_child_wf()
        ensures
            Self::LEVEL.spec_child() == Some(<Self::Child as LevelSpec>::LEVEL),
    ;
}

impl LevelSpec for Lvl<0> {
    const DEPTH: usize = 0;

    const LEVEL: PageLevel = PageLevel::Level0;

    proof fn lemma_wf() {
    }
}

impl LevelSpec for Lvl<1> {
    const DEPTH: usize = 1;

    const LEVEL: PageLevel = PageLevel::Level1;

    proof fn lemma_wf() {
    }
}

impl InnerLevel for Lvl<1> {
    type Child = Lvl<0>;

    proof fn lemma_child_wf() {
    }
}

impl LevelSpec for Lvl<2> {
    const DEPTH: usize = 2;

    const LEVEL: PageLevel = PageLevel::Level2;

    proof fn lemma_wf() {
    }
}

impl InnerLevel for Lvl<2> {
    type Child = Lvl<1>;

    proof fn lemma_child_wf() {
    }
}

impl LevelSpec for Lvl<3> {
    const DEPTH: usize = 3;

    const LEVEL: PageLevel = PageLevel::Level3;

    proof fn lemma_wf() {
    }
}

impl InnerLevel for Lvl<3> {
    type Child = Lvl<2>;

    proof fn lemma_child_wf() {
    }
}

impl LevelSpec for Lvl<4> {
    const DEPTH: usize = 4;

    const LEVEL: PageLevel = PageLevel::Level4;

    proof fn lemma_wf() {
    }
}

impl InnerLevel for Lvl<4> {
    type Child = Lvl<3>;

    proof fn lemma_child_wf() {
    }
}

} // verus!
