//! The "standard library" for [Verus](https://github.com/verus-lang/verus).
//! Contains various utilities and datatypes for proofs,
//! as well as runtime functionality with specifications.
//! For an introduction to Verus, see [the tutorial](https://verus-lang.github.io/verus/guide/).
#![no_std] // don't link the Rust standard library
#![allow(unused_parens)]
#![allow(rustdoc::invalid_rust_codeblocks)]
#![feature(core_intrinsics)]
#![feature(step_trait)]
#![feature(allocator_api)]
extern crate alloc;
pub mod bytes;
pub mod calc_macro;
pub mod map;
pub mod map_lib;
pub mod math;
//pub mod option;
pub mod pervasive;
pub mod relations;
//pub mod result;
pub mod seq;
pub mod seq_lib;
pub mod set;
pub mod set_lib;
pub mod slice;
//pub mod cell;
//pub mod invariant;
//pub mod atomic;
//pub mod atomic_ghost;
pub mod function;
//#[cfg(not(feature = "no_global_allocator"))]
//pub mod ptr;
pub mod layout;
pub mod modes;
pub mod multiset;
pub mod std_specs;
//pub mod state_machine_internal;
//pub mod std_specs;
#[cfg(not(feature = "no_global_allocator"))]
pub mod string;
#[cfg(not(feature = "non_std"))]
pub mod thread;
//#[cfg(not(feature = "no_global_allocator"))]
//pub mod vec;
pub mod view;

// Re-exports all pervasive types, traits, and functions that are commonly used or replace
// regular `core` or `std` definitions.
pub mod prelude;
