use verismo_macro::*;

use crate::tspec::*;
mod memtype;
mod params;
mod memid;

pub use memtype::*;
pub use params::*;
pub use memid::*;

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
}
