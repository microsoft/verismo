#![no_std]
#![cfg_attr(not(verus), allow(dead_code, unused_imports))]

pub mod paging;
pub mod register;
pub use paging::*;
pub use register::*;
