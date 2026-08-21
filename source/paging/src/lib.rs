#![no_std]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]

mod structs;

pub use structs::addr_proof::UniqueAddress;
