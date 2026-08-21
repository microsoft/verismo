// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Copyright (c) Microsoft Corporation
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
use super::{PageSize, Size4KiB};
use builtin_macros::*;
use vstd::prelude::*;

verus! {

pub broadcast group group_types_proof {
    common_proofs::bits::lemma_bit_usize_shl_values,
}

broadcast use group_types_proof;

pub broadcast proof fn lemma_page_size()
    ensures
        #[trigger] <Size4KiB as PageSize>::SIZE == 0x1000,
{
    Size4KiB::lemma_size_wf();
    assert(1usize << 12usize == 0x1000usize) by (compute);
}

} // verus!
