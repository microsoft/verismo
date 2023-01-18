use crate::arch::entities::*;
use crate::tspec::*;

verus! {
    pub trait Model1Eq {
        // self state is derived from other state when hypervisor and other VMPLs may actively change the state.
        spec fn model1_eq(&self, other: &Self, memid: MemID) -> bool;
    }

    pub trait Model2Eq {
        // self state is derived from other state when hypervisor may actively change the state.
        spec fn model2_eq(&self, other: &Self) -> bool;
    }

    pub spec fn spec_attack() -> bool;
}
