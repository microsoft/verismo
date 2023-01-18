use verismo_macro::*;

use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::arch::pgtable::*;
use crate::arch::vram::*;
use crate::tspec::*;

verus!{
#[derive(SpecGetter, SpecSetter)]
pub struct GuestPTRam {
    pub ram: VRamDB,
    pub l0_entry: Map<MemID, SpecGuestPTEntry>,
}

pub struct PTEAccessParam {
    pub memid: MemID,
    pub gvn: GVN,
    pub lvl: PTLevel,
}
}
