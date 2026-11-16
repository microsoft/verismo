//! A page table for four- and five-level paging, in plain Rust. What the OS
//! owes it is in [`structs::PagingAllocator`] and what the architecture owes
//! it in [`structs::ArchPagingMeta`]; [`arch::x86_64`] discharges the latter.
//! The controller uses shared walkers, atomic entry updates, and cfg-selected locking
//! through [`pagetable`].
//!
//! By default, atomic entry updates preserve hardware-updated accessed/dirty
//! bits. `ignore_access_dirty_bits` removes that preservation guarantee.
//! Page-table entries use atomic storage in every configuration.
//! Built-in content locking uses a ticket mutex; `spin-mutex` selects a spin
//! mutex instead. `striped-locks` selects 64 physical-page-keyed locks rather
//! than one global lock.
#![no_std]
#![allow(unused_braces)]

#[cfg(verus_only)]
use vstd::prelude::*;

pub mod arch;
pub mod pagetable;
#[cfg(verus_only)]
mod proofs;
#[cfg(verus_only)]
mod specs;
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
