//! Worked clients for `concurrent_rw`.
#![no_std]
#![cfg_attr(verus_keep_ghost, allow(unexpected_cfgs))]
#![cfg_attr(not(verus_only), allow(dead_code, unused_variables))]

pub mod payload_slot;
pub mod pt;
pub mod pt2;
