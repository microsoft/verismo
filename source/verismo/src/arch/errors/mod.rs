use super::*;
use crate::tspec::*;

verus! {

#[is_variant]
pub enum MemError<Param> {
    Others(Param),  // vaddr, memid
    NoRam(Param),  // vaddr, memid
    NotValidated(Param),  // Failed validation check
    NestedPF(Param),
    PageFault(Param),
    RmpOp(RmpFault, Param),
}

#[is_variant]
pub enum RmpFault {
    Unsupported,
    Size,
    Input,
    Perm,
    DoubleVal,
}

impl<Param> MemError<Param> {
    verus! {
        pub open spec fn trigger_trap(&self) -> bool {
            match *self {
                MemError::RmpOp(fault, _) => {
                    fault === RmpFault::Unsupported
                },
                _ => {
                    true
                }
            }
        }
        pub open spec fn from_err<T>(err: MemError<T>, param: Param) -> Self
        {
            err.with_param(param)
        }

        pub open spec fn with_param<T>(&self, param: T) -> MemError<T>
        {
            match *self {
                MemError::Others(_) => MemError::Others(param),
                MemError::NoRam(_) => MemError::NoRam(param),
                MemError::NotValidated(_) => MemError::NotValidated(param),
                MemError::NestedPF(_) => MemError::NestedPF(param),
                MemError::PageFault(_) => MemError::PageFault(param),
                MemError::RmpOp(fault, _) => MemError::RmpOp(fault, param),
            }
        }
    }
}

} // verus!
