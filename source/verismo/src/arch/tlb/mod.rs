use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::arch::pgtable::*;
use crate::tspec::*;

mod def_s;
pub use def_s::*;
mod tlb_p;
mod tlb_s;
mod tlb_u;
