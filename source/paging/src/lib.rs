//! A page table for four- and five-level paging, in plain Rust. What the OS
//! owes it is in [`os_contract::PagingAllocator`] and what the architecture owes
//! it in [`ArchPagingMeta`]; `arch::x86_64` discharges the latter.
//! The controller uses shared walkers, atomic entry updates, and host locking
//! through [`pagetable`].
//!
//! By default, atomic entry updates preserve hardware-updated accessed/dirty
//! bits. `ignore_access_dirty_bits` removes that preservation guarantee.
//! Page-table entries use atomic storage in every configuration.
#![no_std]
#![allow(unused_braces)]

#[cfg(verus_only)]
use vstd::prelude::*;

mod arch;
#[path = "pagetable_concurrent.rs"]
pub mod pagetable;
#[cfg(verus_only)]
mod proofs;
#[cfg(verus_only)]
mod specs;
mod structs;
pub mod util;

#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::paging::{X86Paging, X86PagingParams};
#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::pt_flags::PTEntryFlags;
#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::tlb::{FlushScope, X86TlbFlushTok};
pub use structs::address;
pub use structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
pub use structs::entry;
pub use structs::frame;
pub use structs::level;
pub use structs::os_contract;
pub use structs::page;
pub use structs::policy;
pub use structs::ptpage;
pub use structs::sizes;
pub use structs::tlb;
