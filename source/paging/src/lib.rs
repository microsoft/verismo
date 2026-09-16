//! A page table for four- and five-level paging, in plain Rust. What the OS
//! owes it is in [`os_contract::PagingAllocator`] and what the architecture owes
//! it in [`ArchPagingMeta`]; `arch::x86_64` discharges the latter.
//! The default `concurrent` feature selects shared walkers, entry updates and
//! host locking through [`pagetable`]; disabling it selects the sequential controller.
//! The selected controllers intentionally have different constructor and lock parameters,
//! so every consumer in one Cargo feature-unification graph must agree on `concurrent`.
//!
//! The default `use_ad` feature supports hardware-updated accessed/dirty bits
//! using atomic entry storage. Disabling `use_ad` presets A/D on present entries
//! instead; importing a tree then requires quiescence and subsequent paging-cache
//! invalidation. Storage is atomic whenever `use_ad` or `concurrent` is enabled.
#![no_std]
#![allow(unused_braces)]

#[cfg(verus_only)]
use vstd::prelude::*;

mod arch;
#[cfg_attr(feature = "concurrent", path = "pagetable_concurrent.rs")]
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
pub use structs::level;
pub use structs::mapping;
pub use structs::os_contract;
pub use structs::policy;
pub use structs::ptpage;
pub use structs::sizes;
pub use structs::tlb;
