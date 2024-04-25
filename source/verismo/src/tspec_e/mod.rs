// math -> size
// size -> array
// size -> stream
#[macro_use]
mod math;
mod array;
mod default;
mod size_e;
mod type_test;

pub use core::mem::*;
pub use core::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Rem, Shl, Shr, Sub};

pub use array::*;
pub use math::*;
pub use size_e::*;
pub use vops::*;

pub use crate::primitives_e::*;
pub use crate::tspec::*;

/*mod array;
mod cast;
mod default;
mod size_e;


//use builtin::*;
pub use cast::*;
pub use default::*;
pub use math::*;
pub use size_e::*;
pub use crate::tspec::*;
*/

/*
pub use crate::pervasive::map::Map;
pub use crate::pervasive::option::*;
pub use crate::pervasive::seq::Seq;
pub use crate::pervasive::set::Set;
pub use crate::pervasive::set_lib;
*/
