// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// What a [`Page`] is, as opposed to what it does.
//
// Textually included into `structs::page`, because the view and the type
// invariant read the private start address and `closed` is module-scoped.
use crate::structs::address::{
    group_addr_proofs, is_aligned_spec, lemma_sign_extend_canonical, pt_idx_spec,
};
use crate::structs::frame::{lemma_align_down_is_aligned, lemma_align_down_stays_above};
use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_is_strictly_smaller, lemma_mod_decreases,
};

verus! {

/// A page is its start address.
impl<S: PageSize> View for Page<S> {
    type V = usize;

    closed spec fn view(&self) -> usize {
        self.start_address@
    }
}

impl<S: PageSize> Page<S> {
    /// Alignment, as a property of the type rather than a clause every caller
    /// has to restate.
    #[verifier::type_invariant]
    pub open spec fn wf(&self) -> bool {
        is_aligned_spec(self@, S::SIZE)
    }

    /// This page's number.
    pub open spec fn spec_page_number(&self) -> usize {
        (self@ / S::SIZE) as usize
    }
}

/// A page's start address is recoverable from its number, which is what makes
/// the two interchangeable as names for the same page.
pub proof fn lemma_page_number_round_trip<S: PageSize>(page: Page<S>)
    requires
        page.wf(),
    ensures
        page@ == page.spec_page_number() * S::SIZE,
{
    S::lemma_size_wf();
    let sz = S::SIZE as int;
    let a = page@ as int;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, sz);
    vstd::arithmetic::mul::lemma_mul_is_commutative(sz, a / sz);
}

/// A page number is far below `usize::MAX`, because a page is at least 4 KiB.
/// [`PageRangeInclusive::len`] needs it to add one without overflowing.
pub proof fn lemma_page_number_lt_max<S: PageSize>(page: Page<S>)
    ensures
        page.spec_page_number() < usize::MAX,
{
    S::lemma_size_wf();
    if page@ > 0 {
        lemma_div_is_strictly_smaller(page@ as int, S::SIZE as int);
    }
}

/// Page numbers are ordered the same way as addresses, which is what stops
/// [`PageRange::len`] from underflowing.
pub proof fn lemma_page_number_ordered<S: PageSize>(lo: Page<S>, hi: Page<S>)
    requires
        lo@ <= hi@,
    ensures
        lo.spec_page_number() <= hi.spec_page_number(),
{
    S::lemma_size_wf();
    lemma_div_is_ordered(lo@ as int, hi@ as int, S::SIZE as int);
}

impl<S: PageSize> PageRange<S> {
    /// The number of pages in the range.
    pub open spec fn spec_len(&self) -> usize {
        if self.start@ < self.end@ {
            (self.end.spec_page_number() - self.start.spec_page_number()) as usize
        } else {
            0
        }
    }
}

impl<S: PageSize> PageRangeInclusive<S> {
    /// The number of pages in the range.
    pub open spec fn spec_len(&self) -> usize {
        if self.start@ <= self.end@ {
            (self.end.spec_page_number() - self.start.spec_page_number() + 1) as usize
        } else {
            0
        }
    }
}

} // verus!
