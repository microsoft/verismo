//! Typed addresses, page geometry, atomic entries, and paging platform contracts.
#![no_std]
#![allow(unused_braces)]

#[cfg(verus_only)]
use vstd::prelude::*;

pub mod arch;
pub mod structs;
mod util;

/// Physical and virtual addresses and alignment helpers.
pub mod address {
    pub use crate::structs::address::{Address, PhysAddr, VirtAddr};
    pub use crate::util::{
        align_down, align_up, is_aligned, overlap, page_align_up, page_offset, round_to_pages,
    };
}

/// Architecture-independent TLB invalidation obligations.
pub mod tlb {
    pub use crate::structs::tlb::{
        with_detach_batch, DetachBatch, FlushedBatch, MayNeedFlush, TlbFlush,
    };
}
