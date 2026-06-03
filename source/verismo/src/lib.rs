#![no_std] // don't link the Rust standard library
#![verifier::deprecated_postcondition_mut_ref_style(true)]
#![allow(macro_expanded_macro_exports_accessed_by_absolute_paths)]
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
#![feature(new_uninit)]
#![feature(core_intrinsics)]

extern crate alloc;

#[macro_use]
pub mod tspec;
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
