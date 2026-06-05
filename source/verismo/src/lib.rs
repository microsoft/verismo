#![no_std] // don't link the Rust standard library
#![verifier::deprecated_postcondition_mut_ref_style(true)]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]
#![allow(unexpected_cfgs)]
#![allow(improper_ctypes_definitions)]
#![allow(unused_variables)]
#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused)]
#![feature(abi_x86_interrupt)]
#![feature(specialization)]
#![allow(incomplete_features)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(never_type)]
#![feature(core_intrinsics)]

extern crate alloc;

// `global size_of usize == 8` must be declared once per crate. The
// declaration in verismo_tspec only governs that crate; we re-declare here so
// constants like `VM_MEM_SIZE = 0x10_0000_0000_0000usize` typecheck.
builtin_macros::verus! {

global size_of usize == 8;

} // verus!
// `tspec` was extracted into the standalone `verismo_tspec` crate so that
// its broadcast groups can auto-propagate to downstream crates via
// `broadcast use verismo_tspec::...;`. The re-export below preserves the
// existing `crate::tspec::X` paths throughout verismo.
pub use verismo_tspec as tspec;
// `macro_const_int!` is the only `#[macro_export]`'d tspec macro used outside
// tspec itself (e.g. arch/*/def_s.rs). Re-export it at the crate root so the
// existing `crate::macro_const_int!` invocations keep working.
pub use verismo_tspec::macro_const_int;

#[macro_use]
mod arch;
mod primitives_e;
//mod trusted_hacl;
mod addr_e;
mod allocator;
mod boot;
mod bsp;
pub mod debug;
mod linkedlist;
mod lock;
mod mem;
mod pgtable_e;
mod ptr; // register -> ptr
#[macro_use]
mod registers;
mod global;
mod mshyper;
mod security;
pub mod snp;
mod trusted_hacl;
mod tspec_e;
mod vbox;
mod vcell;
