// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// What a [`PhysFrame`] is, as opposed to what it does.
//
// Textually included into `structs::frame`, because the view and the type
// invariant read the private start address and `closed` is module-scoped.
use crate::structs::address::{is_aligned_spec, lemma_phys_addr_from_bits};
use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_is_strictly_smaller, lemma_mod_decreases,
    lemma_mod_multiples_basic, lemma_sub_mod_noop_right,
};

verus! {

/// A frame is its start address.
impl<S: PageSize> View for PhysFrame<S> {
    type V = usize;

    closed spec fn view(&self) -> usize {
        self.start_address@
    }
}

impl<S: PageSize> PhysFrame<S> {
    /// Alignment, as a property of the type rather than a clause every caller
    /// has to restate: a frame that did not start a page would make `pfn` lose
    /// a byte offset, and would make two different frames share a number.
    ///
    /// Deliberately `open`: this is the whole public contract of the type, and
    /// a caller reaches it with `use_type_invariant`.
    #[verifier::type_invariant]
    pub open spec fn wf(&self) -> bool {
        is_aligned_spec(self@, S::SIZE)
    }

    /// This frame's number.
    pub open spec fn spec_pfn(&self) -> usize {
        (self@ / S::SIZE) as usize
    }
}

/// A frame's start address is recoverable from its number, which is what makes
/// the two interchangeable as names for the same frame.
pub proof fn lemma_pfn_round_trip<S: PageSize>(frame: PhysFrame<S>)
    requires
        frame.wf(),
    ensures
        frame@ == frame.spec_pfn() * S::SIZE,
{
    S::lemma_size_wf();
    let sz = S::SIZE as int;
    let a = frame@ as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, sz);
    vstd::arithmetic::mul::lemma_mul_is_commutative(sz, a / sz);
}

/// A frame number is far below `usize::MAX`, because a frame is at least 4 KiB.
/// [`PhysFrameRangeInclusive::len`] needs it to add one without overflowing.
pub proof fn lemma_pfn_lt_max<S: PageSize>(frame: PhysFrame<S>)
    ensures
        frame.spec_pfn() < usize::MAX,
{
    S::lemma_size_wf();
    if frame@ > 0 {
        lemma_div_is_strictly_smaller(frame@ as int, S::SIZE as int);
    }
}

/// Aligning down lands on a frame start. Stated over `int` because the callers
/// are proving a `usize` result satisfies it.
pub proof fn lemma_align_down_is_aligned(x: int, m: int)
    requires
        0 < m,
    ensures
        (x - x % m) % m == 0,
{
    lemma_sub_mod_noop_right(x, x, m);
    assert((x - x) % m == 0) by {
        lemma_mod_multiples_basic(0, m);
    }
}

/// Aligning down cannot cross a boundary that is itself aligned. Callers use
/// it to keep a virtual address inside its own canonical half.
pub proof fn lemma_align_down_stays_above(x: int, b: int, m: int)
    requires
        0 < m,
        0 <= b <= x,
        b % m == 0,
    ensures
        x - x % m >= b,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, m);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, m);
    lemma_div_is_ordered(b, x, m);
    vstd::arithmetic::mul::lemma_mul_inequality(b / m, x / m, m);
    vstd::arithmetic::mul::lemma_mul_is_commutative(m, x / m);
    vstd::arithmetic::mul::lemma_mul_is_commutative(m, b / m);
}

/// A multiple of the frame size starts a frame.
pub proof fn lemma_mul_mod_zero(a: int, m: int)
    requires
        0 < m,
    ensures
        (a * m) % m == 0,
{
    lemma_mod_multiples_basic(a, m);
}

/// Frame numbers are ordered the same way as addresses, which is what stops
/// [`PhysFrameRange::len`] from underflowing.
pub proof fn lemma_pfn_ordered<S: PageSize>(lo: PhysFrame<S>, hi: PhysFrame<S>)
    requires
        lo@ <= hi@,
    ensures
        lo.spec_pfn() <= hi.spec_pfn(),
{
    S::lemma_size_wf();
    lemma_div_is_ordered(lo@ as int, hi@ as int, S::SIZE as int);
}

impl<S: PageSize> PhysFrameRange<S> {
    /// The number of frames in the range.
    pub open spec fn spec_len(&self) -> usize {
        if self.start@ < self.end@ {
            (self.end.spec_pfn() - self.start.spec_pfn()) as usize
        } else {
            0
        }
    }
}

impl<S: PageSize> PhysFrameRangeInclusive<S> {
    /// The number of frames in the range.
    pub open spec fn spec_len(&self) -> usize {
        if self.start@ <= self.end@ {
            (self.end.spec_pfn() - self.start.spec_pfn() + 1) as usize
        } else {
            0
        }
    }
}

} // verus!
