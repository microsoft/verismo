mod def;
mod pte;
mod tlb;

pub use def::*;
pub use pte::*;
pub use tlb::*;

use crate::arch::pgtable::*;
use crate::arch::reg::RegName;
use crate::ptr::*;
use crate::registers::CR3;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::DEFINE_BIT_FIELD_GET;
