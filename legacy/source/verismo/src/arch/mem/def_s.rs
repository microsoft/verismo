use verismo_macro::*;

use crate::arch::entities::*;
use crate::arch::pgtable::{SpecGuestPTEntry, SysMap};
use crate::arch::rmp::RmpOp;
use crate::arch::tlb::TLB;
use crate::arch::vram::VRamDB;
use crate::tspec::*;

verus! {

#[derive(SpecGetter, SpecSetter)]
pub struct MemDB {
    pub vram: VRamDB,
    pub l0_entry: Map<MemID, SpecGuestPTEntry>,
    pub sysmap: Map<MemID, SysMap>,
    pub tlb: TLB,
}

} // verus!
