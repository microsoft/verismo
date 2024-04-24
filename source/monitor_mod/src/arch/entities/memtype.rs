use verismo_macro::*;

use super::*;
use crate::arch::addr_s::*;
use crate::tspec::*;

verus! {

#[derive(PartialEq, Eq, Structural, SpecIntEnum)]
#[is_variant]
pub enum PTLevel {
    L3 = 0,
    L2,
    L1,
    L0,
}

/// In Init stage, there is only PTE, SmPrivCode, SmBootData, and some invalidated
/// The Init process transition some invalidated pages to SmPrivData, SmVmplPage, and Others. In this stage, no data flow from private -> others;
/// In PostInit, rmp change is not allowed for any private mem
#[is_variant]
pub enum MemType {
    PTE(PTLevel),  // page table
    SmPrivData,  // heap + secret page
    SmPrivCode,  // code
    SmPrivStack,  // stack
    SmBootData,  // not hidden from Hv
    SmVmplPage,  // shared between other vmpl
    RichOSMem,  // Validated page used by other VMPL
    HvShared,  // Shared page with HV for communication
}

} // verus!
verus! {

impl MemType {
    #[verifier(inline)]
    pub open spec fn is_pt(&self, level: PTLevel) -> bool {
        self === &MemType::PTE(level)
    }

    // Is the data integrity important for SM?
    // Both Hv and VMPL > 0 will fails the SM or will not change content
    #[verifier(inline)]
    pub open spec fn is_sm_int(&self) -> bool {
        ||| self.is_SmPrivData()
        ||| self.is_SmBootData()
        ||| self.is_SmPrivCode()
        ||| self.is_SmPrivStack()
        ||| self.is_PTE()
    }

    // Is the data integrity important for the VM (for all VMPLs)?
    #[verifier(inline)]
    pub open spec fn is_vm_int(&self) -> bool {
        ||| self.is_sm_int()
        ||| self.is_SmVmplPage()
    }

    #[verifier(inline)]
    pub open spec fn need_c_bit(&self) -> bool {
        self.is_vm_int()
        // || self.is_sm_conf()

    }

    // This is a correctness requirement
    #[verifier(inline)]
    pub open spec fn need_c_bit_cleared(&self) -> bool {
        self.is_HvShared()
    }
}

} // verus!
verus! {

/// gpn -> memory type.
/// A software should strictly follows the memory layout defined by this fn.
pub spec fn memtype_inner(gpn: GPN) -> MemType;

pub open spec fn memtype(memid: MemID, gpn: GPN) -> MemType {
    memtype_inner(gpn)
}

} // verus!
#[macro_export]
macro_rules! ASID_FOR_HV {
    () => {
        spec_cast_integer::<u64, nat>(0u64)
    };
}
