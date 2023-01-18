use verismo_macro::*;

use super::perm_s::{PagePerm, Perm, RmpPerm};
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::arch::errors::*;
use crate::tspec::*;
verus!{
#[derive(SpecGetter, SpecSetter)]
pub ghost struct HiddenRmpEntryForPSP {
    pub immutable: bool,
    pub assigned: bool,
    pub validated: bool,
    pub vmsa: bool,
    pub asid: ASID,
    pub gpn: GPN,
    pub size: PageSize,
    pub perms: RmpPerm,
}

#[derive(SpecGetter, SpecSetter)]
pub ghost struct RmpEntry {
    pub val: HiddenRmpEntryForPSP,
}


impl RmpEntry {
    pub proof fn proof_eq(self, r: Self)
    ensures
        (self@ === r@) == (self === r)
    {}
}

pub ghost struct RmpAdjustParam {
    pub gpn: GPN,
    pub psize: PageSize,
    pub vmsa: bool,
    pub vmpl: VMPL,
    pub perms: PagePerm,
}

pub ghost struct PvalidateParam {
    pub gpn: GPN,
    pub psize: PageSize,
    pub val: bool,
}

pub type RmpUpdateParam = RmpEntry;
pub type RmpMap = Map<SPN, RmpEntry>;

#[is_variant]
pub ghost enum RmpOp<AddrT> {
    RmpAdjust(PageID<AddrT>, RmpAdjustParam),
    Pvalidate(PageID<AddrT>, PvalidateParam),
    RmpUpdate(PageID<AddrT>, RmpUpdateParam),
}

crate::macro_const_int! {
    #[macro_export]
    pub const RMP_FAIL_INPUT: u64 = 1;
    #[macro_export]
    pub const RMP_FAIL_PERMISSION: u64 = 2;
    #[macro_export]
    pub const RMP_FAIL_INUSE: u64 = 3;
    #[macro_export]
    pub const RMP_FAIL_OVERLAP: u64 = 4;
    #[macro_export]
    pub const RMP_FAIL_SIZEMISMATCH: u64 = 6;
}
}
