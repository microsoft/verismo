use verismo_macro::*;

use crate::tspec::*;
mod memid;
mod memtype;
mod params;

pub use memid::*;
pub use memtype::*;
pub use params::*;

verus! {

pub type ASID = nat;

pub type CPU = nat;

#[derive(PartialEq, Eq, SpecIntEnum, Copy, Clone)]
#[is_variant]
pub enum VMPL {
    VMPL0,
    VMPL1,
    VMPL2,
    VMPL3,
}

} // verus!
