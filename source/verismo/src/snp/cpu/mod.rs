mod gdt;
mod vmsa;

pub use gdt::*;
pub use vmsa::*;

use crate::snp::ghcb::{vc_terminate_debug, SM_TERM_INVALID_PARAM};
use crate::tspec::*;
use crate::tspec_e::*;
use crate::*;
