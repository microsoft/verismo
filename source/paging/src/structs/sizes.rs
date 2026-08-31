// SPDX-License-Identifier: MIT OR Apache-2.0
use builtin_macros::*;
use vstd::prelude::*;

#[cfg(verus_only)]
#[path = "../proofs/sizes.rs"]
mod sizes_spec_defs;
#[cfg(verus_only)]
pub use sizes_spec_defs::*;
#[cfg(verus_only)]
verus! {

broadcast use sizes_spec_defs::group_types_proof;

} // verus!
verus! {

/// Marker type describing the width of the in-page byte offset, i.e. the page
/// shift.
///
/// The shift is at least 12 because every architecture this models -- x86,
/// AArch64 and RISC-V -- has a 4 KiB smallest page. That bound is what makes a
/// table page hold at least one entry.
pub trait PageOffset {
    const SHIFT: usize;

    proof fn lemma_shift_wf()
        ensures
            12 <= Self::SHIFT < usize::BITS,
            common_proofs::bits::is_pow_of_2((1usize << Self::SHIFT) as u64),
    ;
}

/// Marker type describing the size of a page, following the `x86_64` crate's
/// `PageSize` trait.
pub trait PageSize: PageOffset {
    const SIZE: usize;

    proof fn lemma_size_wf()
        ensures
            Self::SIZE == 1usize << Self::SHIFT,
            12 <= Self::SHIFT < usize::BITS,
            Self::SIZE >= 4096usize,
            common_proofs::bits::is_pow_of_2(Self::SIZE as u64),
    ;
}

} // verus!
verus! {

pub struct Size4KiB;

pub struct Size2MiB;

pub struct Size1GiB;

impl PageOffset for Size4KiB {
    const SHIFT: usize = 12;

    proof fn lemma_shift_wf() {
        assert(Self::SHIFT == 12);
        assert(1usize << 12usize == 0x1000usize) by (compute);
        assert(common_proofs::bits::is_pow_of_2(0x1000u64)) by (compute);
    }
}

impl PageOffset for Size2MiB {
    const SHIFT: usize = 21;

    proof fn lemma_shift_wf() {
        assert(Self::SHIFT == 21);
        assert(1usize << 21usize == 0x20_0000usize) by (compute);
        assert(common_proofs::bits::is_pow_of_2(0x20_0000u64)) by (compute);
    }
}

impl PageOffset for Size1GiB {
    const SHIFT: usize = 30;

    proof fn lemma_shift_wf() {
        assert(Self::SHIFT == 30);
        assert(1usize << 30usize == 0x4000_0000usize) by (compute);
        assert(common_proofs::bits::is_pow_of_2(0x4000_0000u64)) by (compute);
    }
}

impl<T: PageOffset> PageSize for T {
    const SIZE: usize = 1usize << T::SHIFT;

    proof fn lemma_size_wf() {
        T::lemma_shift_wf();
        let shift = T::SHIFT;
        assert(Self::SIZE == 1usize << shift);
        assert(1usize << shift >= 4096usize) by (bit_vector)
            requires
                12 <= shift < 64,
        ;
    }
}

/// The smallest page this build maps.
///
/// A property of the machine the kernel is built for, not of the paging code:
/// one binary targets one machine, so a build-wide choice is both simpler and
/// more honest than a trait member every architecture would separately have to
/// agree on. Nothing selected means 4 KiB, which every architecture this models
/// supports.
#[cfg(not(any(feature = "min-page-2mib", feature = "min-page-1gib")))]
pub type MinPageSize = Size4KiB;

#[cfg(feature = "min-page-2mib")]
pub type MinPageSize = Size2MiB;

#[cfg(feature = "min-page-1gib")]
pub type MinPageSize = Size1GiB;

#[cfg(all(feature = "min-page-2mib", feature = "min-page-1gib"))]
compile_error!("min-page-2mib and min-page-1gib select different page sizes");

/// Width of the in-page byte offset, in bits.
///
/// Spelled out rather than written `<MinPageSize as PageOffset>::SHIFT`, which
/// Verus cannot evaluate in a `const`. [`lemma_min_page_wf`] proves the
/// geometry facts consumers need from the spelled-out numbers.
#[cfg(not(any(feature = "min-page-2mib", feature = "min-page-1gib")))]
pub const PAGE_OFFSET_WIDTH: usize = 12;

#[cfg(feature = "min-page-2mib")]
pub const PAGE_OFFSET_WIDTH: usize = 21;

#[cfg(feature = "min-page-1gib")]
pub const PAGE_OFFSET_WIDTH: usize = 30;

/// Bytes in the smallest page. Also spelled out, because Verus checks a `const`
/// body for overflow and cannot be given a proof to do it with.
#[cfg(not(any(feature = "min-page-2mib", feature = "min-page-1gib")))]
pub const PAGE_SIZE: usize = 0x1000;

#[cfg(feature = "min-page-2mib")]
pub const PAGE_SIZE: usize = 0x20_0000;

#[cfg(feature = "min-page-1gib")]
pub const PAGE_SIZE: usize = 0x4000_0000;

/// The geometry facts [`PageSize::lemma_size_wf`] would give for the selected
/// marker, proved from the spelled-out numbers instead.
///
/// Not routed through the trait: `MinPageSize` is concrete, and asking Verus for
/// a blanket impl's associated const on a concrete type makes rustc evaluate its
/// body, which Verus cannot erase.
pub proof fn lemma_min_page_wf()
    ensures
        PAGE_SIZE == 1usize << PAGE_OFFSET_WIDTH,
        12 <= PAGE_OFFSET_WIDTH < usize::BITS,
        PAGE_SIZE >= 4096,
        common_proofs::bits::is_pow_of_2(PAGE_SIZE as u64),
{
    assert(PAGE_SIZE == 1usize << PAGE_OFFSET_WIDTH) by (compute);
    assert(PAGE_SIZE >= 4096) by (compute);
    assert(common_proofs::bits::is_pow_of_2(PAGE_SIZE as u64)) by (compute);
}

/// Bridges the 4KB marker to the literal page geometry used by the `pfn`
/// specifications.
pub proof fn lemma_size_4k()
    ensures
        <Size4KiB as PageSize>::SIZE == 0x1000usize,
        <Size4KiB as PageOffset>::SHIFT == 12usize,
{
    Size4KiB::lemma_size_wf();
    assert(1usize << 12usize == 0x1000usize) by (compute);
}

} // verus!
