//! Turning an address into the slot a level's table page holds for it.
//!
//! One function, used by every level: the level is a value, so the index
//! arithmetic is ordinary arithmetic rather than a family of constants
//! generated per level. `entry_index_at` is the same function for a caller
//! whose level is fixed when the crate is compiled; it takes the level as a
//! const parameter and delegates, so there is still only one definition of
//! what an entry index is.
use builtin_macros::{proof, verus_spec, verus_verify};
use vstd::prelude::*;

use crate::structs::address::{Address, VirtAddr};
use crate::structs::arch_contract::ArchPagingMeta;
#[cfg(verus_only)]
use crate::structs::arch_contract::{level_geometry_wf, level_shift, spec_entry_index};
use crate::structs::entry::PTEntry;
use crate::structs::level::PageLevel;
use crate::structs::ptpage::PTPage;
#[cfg(verus_only)]
use vstd::bits::low_bits_mask;

#[cfg(verus_only)]
use crate::structs::sizes::lemma_min_page_wf;
use crate::structs::sizes::{
    MinPageSize, PageOffset, ENTRY_COUNT, PAGE_OFFSET_WIDTH, PAGE_TABLE_INDEX_WIDTH,
};

#[verus_verify]
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
    ensures
        ret == level_shift(level.depth() as nat),
        ret < usize::BITS,
)]
pub fn shift_at<A: ArchPagingMeta>(level: PageLevel) -> usize {
    proof! { lemma_level_shift_monotone::<A>(level); }
    PAGE_OFFSET_WIDTH + level.depth() * PAGE_TABLE_INDEX_WIDTH
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
    proof! { lemma_index_mask_is_mod(vaddr >> shift); }
    (vaddr >> shift) & INDEX_MASK
}

/// The entry `vaddr` selects at the level fixed by `L`, counted from the leaf.
///
/// Deliberately not `VirtAddr::to_pgtbl_idx`, which spells out x86-64's shift
/// and mask: only the level moves into the type here, and the geometry still
/// comes from the page size this build was given.
#[verus_verify]
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        L <= 4,
    ensures
        ret == spec_entry_index::<A>(vaddr, PageLevel::from_nat(L as nat)),
        ret < PTPage::<A>::count(),
)]
pub const fn pt_entry_index_bits<A: ArchPagingMeta, const L: usize>(vaddr: usize) -> usize {
    proof! {
        PageLevel::lemma_from_nat_depth(L as nat);
        lemma_level_shift_monotone::<A>(PageLevel::from_nat(L as nat));
        lemma_per_page_positive::<A>();
    }
    // `let`, not an inner `const` item: that cannot name the outer `L` (E0401).
    // It costs nothing -- `L` is fixed at monomorphization, so the shift folds
    // to an immediate before codegen.
    let shift = PAGE_OFFSET_WIDTH + L * PAGE_TABLE_INDEX_WIDTH;
    proof! { lemma_index_mask_is_mod(vaddr >> shift); }
    (vaddr >> shift) & INDEX_MASK
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

#[verus_verify]
#[verus_spec(ret =>
    requires
        level_geometry_wf::<A>(),
        L <= 4,
    ensures
        ret == spec_entry_index::<A>(vaddr@, PageLevel::from_nat(L as nat)),
        ret < PTPage::<A>::count(),
)]
pub fn entry_index_at<A: ArchPagingMeta, const L: usize>(vaddr: VirtAddr) -> usize {
    pt_entry_index_bits::<A, L>(vaddr.bits())
}

verus! {

/// Masking with the low index bits is what selecting an entry *is*; the
/// specification says it with `%` because that is easier to reason about.
///
/// Written by shifting in ones rather than as `(1 << WIDTH) - 1`: Verus checks
/// a `const` body for overflow and offers nowhere to attach the proof that the
/// subtraction cannot underflow.
///
/// The parentheses in the `- 1` form would matter too -- in Rust `-` binds
/// tighter than `<<`, so `1usize << PAGE_TABLE_INDEX_WIDTH - 1` is a single bit
/// rather than a mask.
pub const INDEX_MASK: usize = !(usize::MAX << PAGE_TABLE_INDEX_WIDTH);

/// Masking off the low index bits agrees with taking the remainder, because a
/// table page holds a power of two entries.
pub proof fn lemma_index_mask_is_mod(x: usize)
    ensures
        (x & INDEX_MASK) == x % (ENTRY_COUNT as usize),
        (x & INDEX_MASK) < ENTRY_COUNT,
{
    lemma_min_page_wf();
    assert(INDEX_MASK as nat + 1 == ENTRY_COUNT as nat) by (compute);
    assert(low_bits_mask(PAGE_TABLE_INDEX_WIDTH as nat) == INDEX_MASK as nat);
    vstd::bits::lemma_usize_low_bits_mask_is_mod(x, PAGE_TABLE_INDEX_WIDTH as nat);
}

/// A shallower level shifts by less, so bounding the deepest level bounds them
/// all -- which is what makes every index a walk computes a legal shift.
pub proof fn lemma_level_shift_monotone<A: ArchPagingMeta>(level: PageLevel)
    requires
        level_geometry_wf::<A>(),
    ensures
        level_shift(level.depth() as nat) == PAGE_OFFSET_WIDTH + level.depth() as nat
            * PAGE_TABLE_INDEX_WIDTH,
        level_shift(level.depth() as nat) <= level_shift(PageLevel::Level4.depth() as nat)
            < usize::BITS,
{
    PageLevel::lemma_depth_roundtrip(level);
    PageLevel::lemma_depth_roundtrip(PageLevel::Level4);
    vstd::arithmetic::mul::lemma_mul_inequality(
        level.depth() as nat as int,
        PageLevel::Level4.depth() as nat as int,
        PAGE_TABLE_INDEX_WIDTH as int,
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
    lemma_min_page_wf();
}

} // verus!
