//! Which level of the tree a table page sits at, as a value ([`PageLevel`]) and
//! as a type ([`Lvl`]). Level 0 is the leaf; the root of a four-level tree is
//! level 3.
use crate::structs::geometry::level_size;

/// The level of a page-table page, counted from the leaf. x86 walks at most
/// five levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PageLevel {
    Level0,
    Level1,
    Level2,
    Level3,
    Level4,
}

impl PageLevel {
    /// How many levels lie below this one. The leaf level is 0.
    pub fn depth(&self) -> usize {
        match self {
            PageLevel::Level0 => 0,
            PageLevel::Level1 => 1,
            PageLevel::Level2 => 2,
            PageLevel::Level3 => 3,
            PageLevel::Level4 => 4,
        }
    }

    /// The level one step down, or `None` at the leaf. Refusing to descend past
    /// level 0 is not a convenience: there the hardware reads bit 7 as PAT
    /// rather than PS, so an entry that looks like a table pointer is a
    /// mapping.
    pub fn child(&self) -> Option<PageLevel> {
        match self {
            PageLevel::Level0 => None,
            PageLevel::Level1 => Some(PageLevel::Level0),
            PageLevel::Level2 => Some(PageLevel::Level1),
            PageLevel::Level3 => Some(PageLevel::Level2),
            PageLevel::Level4 => Some(PageLevel::Level3),
        }
    }

    /// The level one step up, saturating at level 4.
    pub fn parent(&self) -> PageLevel {
        match self {
            PageLevel::Level0 => PageLevel::Level1,
            PageLevel::Level1 => PageLevel::Level2,
            PageLevel::Level2 => PageLevel::Level3,
            PageLevel::Level3 => PageLevel::Level4,
            PageLevel::Level4 => PageLevel::Level4,
        }
    }

    /// How much address space one entry at this level covers.
    pub fn size(&self) -> usize {
        level_size(*self)
    }

    pub fn is_leaf(&self) -> bool {
        matches!(self, PageLevel::Level0)
    }

    /// The level at depth `L`, for a caller whose level is fixed at compile
    /// time. Depths above 4 saturate, as no architecture here names one.
    pub const fn at<const L: usize>() -> PageLevel {
        match L {
            0 => PageLevel::Level0,
            1 => PageLevel::Level1,
            2 => PageLevel::Level2,
            3 => PageLevel::Level3,
            _ => PageLevel::Level4,
        }
    }
}

/// A level of the tree as a type: `L` is the depth above the leaf, so `Lvl<0>`
/// is the leaf and `Lvl<4>` the root of a five-level tree. The numbering
/// matches `PageLevel::depth` and the shift in `geometry::shift_at`.
pub struct Lvl<const L: usize>;

/// What a level marker knows: its depth, and the same level as a value.
pub trait LevelSpec: 'static {
    const DEPTH: usize;

    const LEVEL: PageLevel;
}

/// A level with another level beneath it. `Lvl<0>` has no impl, so descending
/// below the leaf is a type error.
pub trait InnerLevel: LevelSpec {
    type Child: LevelSpec;
}

impl LevelSpec for Lvl<0> {
    const DEPTH: usize = 0;

    const LEVEL: PageLevel = PageLevel::Level0;
}

impl LevelSpec for Lvl<1> {
    const DEPTH: usize = 1;

    const LEVEL: PageLevel = PageLevel::Level1;
}

impl InnerLevel for Lvl<1> {
    type Child = Lvl<0>;
}

impl LevelSpec for Lvl<2> {
    const DEPTH: usize = 2;

    const LEVEL: PageLevel = PageLevel::Level2;
}

impl InnerLevel for Lvl<2> {
    type Child = Lvl<1>;
}

impl LevelSpec for Lvl<3> {
    const DEPTH: usize = 3;

    const LEVEL: PageLevel = PageLevel::Level3;
}

impl InnerLevel for Lvl<3> {
    type Child = Lvl<2>;
}

impl LevelSpec for Lvl<4> {
    const DEPTH: usize = 4;

    const LEVEL: PageLevel = PageLevel::Level4;
}

impl InnerLevel for Lvl<4> {
    type Child = Lvl<3>;
}
