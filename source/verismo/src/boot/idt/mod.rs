mod def;
mod dummy;
mod idt_reg_t;

pub use def::*;
pub use dummy::*;

use crate::arch::reg::RegName;
use crate::global::*;
use crate::ptr::*;
use crate::registers::*;
use crate::tspec::*;
use crate::tspec_e::*;
