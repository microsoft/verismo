use super::*;
use crate::tspec_e::*;

verus!{
#[derive(ExecStruct, NotPrimitive, VTypeCastSec, VTypeCast, SpecSize, WellFormed, IsConstant)]
#[repr(C, align(1))]
pub struct PageTableEntry<T> {
    pub value: crate::tspec_e::u64_s,
    pub dummy: Ghost<T>,
}
}

verus! {
    impl<T> PageTableEntry<T> {
        pub open spec fn view(&self) -> SpecPageTableEntry<T> {
            SpecPageTableEntry {
                value: self.value.vspec_cast_to(),
                dummy: self.dummy,
            }
        }
    }
}