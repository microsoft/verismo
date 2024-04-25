mod array_e;
mod array_s;
mod array_t;
pub mod array_utils;
mod sort;

//pub use s::*;
pub use array_e::*;
use array_t::*;

use super::*;

pub type IndexType = usize;

crate::macro_const_int! {
    #[macro_export]
    pub const U32_MAX: u32 = 0xffff_ffff;//4294967295u32;
}

verismo! {
#[derive(Copy)]
#[repr(C)]
#[verifier(external_body)]
#[verifier::accept_recursive_types(T)]
pub struct Array<T, const N: usize> {
    pub array: [T; N],
}
}
