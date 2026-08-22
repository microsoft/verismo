#![no_std]
#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]
#![cfg_attr(verus_only, verifier::allow(unknown_automatic_derive))]
#![cfg_attr(verus_only, allow(macro_expanded_macro_exports_accessed_by_absolute_paths))]
#![allow(unused_braces)]

use builtin_macros::*;

mod arch;
mod proofs;
pub mod specs;
mod structs;
pub mod util;

#[cfg(target_arch = "x86_64")]
pub use arch::x86_64::reg_contract::{
    cpl_precondition, cr0_paging_precondition, cr3_paging_precondition, cr4_paging_precondition,
    efer_paging_precondition, efer_value, geometry_paging_precondition, low_bits_mask_u64,
    paging_inv, paging_view, PagingView, MSR_EFER,
};
pub use proofs::address_space::UniqueAddress;
pub use structs::address;
pub use structs::arch_contract::{
    page_offset_width, ArchPagingGeometry, ArchPagingMeta, GenericPageTableFlags,
};
pub use structs::concurrent_pt;
pub use structs::entry;
pub use structs::handle;
pub use structs::host_contract;
pub use structs::level;
pub use structs::sizes;

verus! {

global size_of usize == 8;

} // verus!
