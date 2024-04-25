use super::*;
use crate::*;

verus! {

#[is_variant]
pub enum MemID {
    Guest(nat, VMPL),
    Hv,
}

pub struct CpuMemID(pub CPU, pub MemID);

verus! {
    impl CpuMemID {
        pub open spec fn cpu(&self) -> CPU {
            self.0
        }

        pub open spec fn memid(&self) -> MemID {
            self.1
        }
    }
}

verus! {
pub open spec fn current_vmpl() -> VMPL {
    VMPL::VMPL0
}

impl MemID {
    pub open spec fn is_sm(&self, sm_memid: MemID) -> bool {
        &&& self.to_vmpl().as_int() <= sm_memid.to_vmpl().as_int()
        &&& (self.to_asid() === sm_memid.to_asid())
    }

    pub open spec fn is_vmpl0(&self) -> bool {
        self.to_vmpl().is_VMPL0() && self.is_Guest()
    }

    pub open spec fn to_asid(&self) -> ASID {
        match *self {
            MemID::Guest(id_minus_one, _,) => {
                id_minus_one + 1
            }
            _ => {
                ASID_FOR_HV!()
            }
        }
    }

    pub open spec fn to_vmpl(&self) -> VMPL
    recommends
        self.is_Guest()
    {
        match *self {
            MemID::Guest(_, vmpl) => {
                vmpl
            }
            _ => {
                VMPL::VMPL0
            }
        }
    }
}
}

} // verus!
