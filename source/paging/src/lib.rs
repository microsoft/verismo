//! A page table for four- and five-level paging, in plain Rust. What the OS
//! owes it is in [`os_contract::PagingHandler`] and what the architecture owes
//! it in [`ArchPagingMeta`]; `arch::x86_64` discharges the latter.
#![no_std]
#![allow(unused_braces)]

mod arch;
pub mod pagetable;
mod structs;
pub mod util;

#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::paging::{X86Paging, X86PagingParams};
#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::pt_flags::PTEntryFlags;
pub use structs::address;
pub use structs::arch_contract::{ArchPagingMeta, GenericPageTableFlags};
pub use structs::entry;
pub use structs::geometry;
pub use structs::level;
pub use structs::os_contract;
pub use structs::ptpage;
pub use structs::sizes;
pub use structs::tlb;
