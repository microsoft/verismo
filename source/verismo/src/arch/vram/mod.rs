use crate::arch::addr_s::*;
use crate::arch::attack::*;
use crate::arch::entities::*;
use crate::arch::errors::*;
use crate::arch::memop::MemOp;
use crate::arch::pgtable::*;
use crate::arch::rmp::perm_s::Perm;
use crate::arch::rmp::*;
use crate::tspec::*;
use crate::*;

pub mod def;
mod vram_rmp_p;
pub use def::*;

mod vram_p;
pub mod vram_s;
