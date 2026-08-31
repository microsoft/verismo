//! Turning an address into the slot a level's table page holds for it.
//!
//! One function, used by every level: the level is a value, so the index
//! arithmetic is ordinary arithmetic rather than a family of constants
//! generated per level.
use builtin_macros::{proof, verus_spec, verus_verify};
use vstd::prelude::*;

use crate::structs::address::{Address, VirtAddr};
use crate::structs::arch_contract::{
    level_geometry_wf, level_index_width, level_shift, spec_entry_index, ArchPagingMeta,
};
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::ptpage::PTPage;
use crate::structs::sizes::{MinPageSize, PageOffset, PAGE_OFFSET_WIDTH};

#[verus_verify]
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
    ensures
        ret == level_shift::<A>(level.depth() as nat),
        ret < usize::BITS,
)]
pub fn shift_at<A: ArchPagingMeta>(level: PageLevel) -> usize {
    proof! { lemma_level_shift_monotone::<A>(level); }
    PAGE_OFFSET_WIDTH + level.depth() * A::index_width()
}

#[verus_verify]
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
    ensures
        ret == spec_entry_index::<A>(vaddr, level),
        ret < PTPage::<A>::count(),
)]
pub fn entry_index_bits<A: ArchPagingMeta>(vaddr: usize, level: PageLevel) -> usize {
    let shift = shift_at::<A>(level);
    let count = A::entries_per_page();
    proof! { lemma_per_page_positive::<A>(); }
    (vaddr >> shift) % count
}

#[verus_verify]
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
    ensures
        ret == spec_entry_index::<A>(vaddr@, level),
        ret < PTPage::<A>::count(),
)]
pub fn entry_index<A: ArchPagingMeta>(vaddr: VirtAddr, level: PageLevel) -> usize {
    entry_index_bits::<A>(vaddr.bits(), level)
}

verus! {

/// A shallower level shifts by less, so bounding the deepest level bounds them
/// all -- which is what makes every index a walk computes a legal shift.
pub proof fn lemma_level_shift_monotone<A: ArchPagingMeta>(level: PageLevel)
    requires
        level_geometry_wf::<A>(),
    ensures
        level_shift::<A>(level.depth() as nat) == PAGE_OFFSET_WIDTH + level.depth() as nat
            * level_index_width::<A>(),
        level_shift::<A>(level.depth() as nat) <= level_shift::<A>(PageLevel::Level4.depth() as nat)
            < usize::BITS,
{
    PageLevel::lemma_depth_roundtrip(level);
    PageLevel::lemma_depth_roundtrip(PageLevel::Level4);
    vstd::arithmetic::mul::lemma_mul_inequality(
        level.depth() as nat as int,
        PageLevel::Level4.depth() as nat as int,
        level_index_width::<A>() as int,
    );
}

/// A table page holds at least one entry, so an index modulo the count is a
/// legal index.
pub proof fn lemma_per_page_positive<A: ArchPagingMeta>()
    requires
        level_geometry_wf::<A>(),
    ensures
        PTPage::<A>::count() > 0,
{
    vstd::arithmetic::power2::lemma_pow2_pos(level_index_width::<A>());
}

} // verus!
