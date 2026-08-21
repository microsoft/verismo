//! Proof helpers shared across the verified crates in this workspace.
#![no_std]
#![allow(unused_braces)]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]

use builtin_macros::*;

pub mod bits;

verus! {

global size_of usize == 8;

} // verus!
