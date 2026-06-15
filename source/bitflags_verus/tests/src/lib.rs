// SPDX-License-Identifier: MIT
//! Demonstration tests for `bitflags_verus!` showing how the macro provides
//! Verus specifications for bitflags-generated types.
//!
//! Tests cover four underlying bit types: u32, usize, i32, isize.
//! All assertions are relational (no concrete value checks).
#![no_std]

pub mod test_i32;
pub mod test_isize;
pub mod test_u32;
pub mod test_usize;
pub mod test_verus_spec;
