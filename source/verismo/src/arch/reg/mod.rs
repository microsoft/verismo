use verismo_macro::*;

use crate::tspec::*;

verus! {

#[is_variant]
pub enum RegName {
    // register fields
    Rflags,
    Rax,
    Rsp,
    Cs,
    Ds,
    Ss,
    Es,
    Gs,
    Cpl,
    Cr0,
    Cr1,
    Cr2,
    Cr3,
    Cr4,
    XCr0,
    IdtrBaseLimit,
    GdtrBaseLimit,
    MSR(u32),
}

#[derive(SpecIntEnum)]
#[is_variant]
pub enum RflagBit {
    CF = 0,  // Carry flag
    R1 = 1,
    PF = 2,
    R2 = 3,
    AF = 4,
    R3 = 5,
    ZF = 6,
    SF = 7,
    TF = 8,  // Trap flag
    IF = 9,  // Interrupt enable flag
    DF = 10,
    ID = 21,  // Able to use CPUID
}

pub const MSR_GHCB_BASE: u32 = 0xc0010130u32;

pub const MSR_GS_BASE: u32 = 0xc0000101u32;

pub const MSR_EFER_BASE: u32 = 0xc0000080;

pub const MSR_SEV_STATUS: u32 = 0xc0010131u32;

} // verus!
impl RegName {
    verus! {

pub open spec fn spec_is_shared(&self) -> bool {
    match *self {
        RegName::MSR(regval) if regval == MSR_GHCB_BASE => true,
        _ => false,
    }
}

} // verus!
}

pub type RegValType = u64;

pub type RegDB = FMap<RegName, RegValType>;

verus! {

impl RegDB {
    pub open spec fn reg_inv(&self) -> bool {
        &&& self[RegName::Cpl] == 0
    }
}

} // verus!
