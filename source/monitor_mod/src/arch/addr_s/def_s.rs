use super::*;
use crate::tspec_e::*;

verus! {

global size_of usize == 8;

#[derive(Copy, Clone, VTypeCast, ExecStruct, NotPrimitive, VTypeCastSec, SpecSize, WellFormed, IsConstant)]
pub struct GuestVir;

#[derive(Copy, Clone, VTypeCast, ExecStruct, NotPrimitive, VTypeCastSec, SpecSize, WellFormed, IsConstant)]
pub struct GuestPhy;

#[derive(Copy, Clone, VTypeCast, ExecStruct, NotPrimitive, VTypeCastSec, SpecSize, WellFormed, IsConstant)]
pub struct SysPhy;

pub trait AddrType {

}

impl AddrType for GuestVir {

}

impl AddrType for GuestPhy {

}

impl AddrType for SysPhy {

}

pub type SizeType = u64;

/// 4K Page
#[verifier::ext_equal]
pub struct SpecPage<T> {
    pub value: nat,
    pub dummy: Ghost<T>,
}

// T: AddrType
#[verifier::ext_equal]
pub struct SpecAddr<T> {
    pub value: nat,
    pub dummy: Ghost<T>,
}

// T: AddrType
pub struct SpecMem<T> {
    pub first: SpecAddr<T>,
    pub size: nat,
}

pub type GVN = SpecPage<GuestVir>;

pub type GPN = SpecPage<GuestPhy>;

pub type SPN = SpecPage<SysPhy>;

pub type GVA = SpecAddr<GuestVir>;

pub type GPA = SpecAddr<GuestPhy>;

pub type SPA = SpecAddr<SysPhy>;

pub type GVMem = SpecMem<GuestVir>;

pub type GPMem = SpecMem<GuestPhy>;

pub type SPMem = SpecMem<SysPhy>;

// VM constants
// Need to publish those constant if it is used in verification;
// otherwise, the root module will not understand those constant in spec.
//#[allow(unused_variables)]
crate::macro_const_int! {
    #[macro_export]
    #[verifier::publish]
    pub const PAGE_SHIFT: usize = 12usize;
    #[macro_export]
    #[verifier::publish]
    pub const PAGE_SIZE: usize = 0x1000usize;
    #[macro_export]
    #[verifier::publish]
    pub const PAGE_2M_SIZE: usize = 0x200000usize;
    #[macro_export]
    #[verifier::publish]
    pub const VM_MEM_SIZE: usize = 0x10_0000_0000_0000usize;
    #[macro_export]
    #[verifier::publish]
    pub const VM_PAGE_NUM: usize = 0x100_0000_0000usize;
    #[macro_export]
    #[verifier::publish]
    pub const BLOCK_SIZE: usize = 1usize;
}

#[is_variant]
#[derive(Copy, Clone, PartialEq, Eq, SpecIntEnum)]
pub enum PageSize {
    Size4k = 0,
    Size2m = 1,
}

verus! {
impl PageSize {
    pub open spec fn size(&self) -> int
    {
        match self {
            PageSize::Size4k => {
                PAGE_SIZE!()
            },
            PageSize::Size2m => {
                PAGE_2M_SIZE!()
            }
        }
    }
}
}

} // verus!
