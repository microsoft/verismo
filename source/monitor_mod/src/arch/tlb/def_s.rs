use verismo_macro::*;

use crate::arch::addr_s::*;
use crate::arch::entities::MemID;
use crate::arch::pgtable::*;
use crate::tspec::*;

verus! {

/// Define TLB as a structural struct;
/// Use the hidden private int to represent the instance
/// but will never use the hidden int directly
#[derive(SpecSetter, SpecGetter)]
pub struct TLB {
    pub db: FMap<MemID, Map<GVN, SpecGuestPTEntry>>,
}

pub struct TLBIdx(pub MemID, pub GVN);

} // verus!
