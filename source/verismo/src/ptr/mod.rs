use core::mem::MaybeUninit;
use core::{marker, mem};

use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::tspec::*;
extern crate alloc;

mod def_s;
mod ptr_s;
mod ptr_t;
mod ptr_u;
mod snp;

mod ptr_e;
mod raw_ptr_s;
mod raw_ptr_t;

pub use def_s::*;
pub use ptr_s::inv_snp_value;
pub use ptr_t::*;
pub use raw_ptr_s::*;
pub use raw_ptr_t::*;
pub use snp::*;

use crate::tspec_e::*;
