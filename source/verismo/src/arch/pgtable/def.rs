use verismo_macro::*;

use super::*;
use crate::arch::addr_s::*;
use crate::arch::entities::*;
use crate::tspec::*;

#[macro_export]
macro_rules! BIT64 {
    ($x: expr) => {
        (1u64 << (($x) as u64))
    };
}

verus! {

#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(PT)]
pub ghost struct MemMap<T, PT> {
    pub db: Map<SpecPage<T>, SpecPageTableEntry<PT>>,
}

pub type SysMap = MemMap<GuestPhy, SysPhy>;

pub type GuestMap = MemMap<GuestVir, GuestPhy>;

pub spec const MAX_PT_LEVEL: PTLevel = PTLevel::L0;

#[derive(Eq, PartialEq, Structural, SpecIntEnum)]
#[is_variant]
pub enum PteFlag {
    P = 0,  // Present
    W = 1,  // Write
    S = 2,  // Allow both user/supervisor
    PWT = 3,  // Writethrough
    PCD = 4,  // Cache disable
    A = 5,  // Accessed
    D = 6,  // Dirty
    C = 51,  // Encryption
    NX = 63,  // No-execute
}

#[derive(SpecGetter)]
pub ghost struct SpecPageTableEntry<T> {
    pub value: int,
    pub dummy: Ghost<T>,
}

pub struct PTEAccessParam {
    pub memid: MemID,
    pub gvn: GVN,
    pub lvl: PTLevel,
}

pub type SpecGuestPTEntry = SpecPageTableEntry<GuestPhy>;

pub type SpecSysPTEntry = SpecPageTableEntry<SysPhy>;

pub type GuestPTEntry = PageTableEntry<GuestPhy>;

pub type SysPTEntry = PageTableEntry<SysPhy>;

} // verus!
verus! {

pub const PT_ENTRY_SIZE: u64 = 8u64;

} // verus!
crate::macro_const! {
    #[macro_export]
    pub const L3_OFFSET: u64 = 39u64;
    #[macro_export]
    pub const L2_OFFSET: u64 = 30u64;
    #[macro_export]
    pub const L1_OFFSET: u64 = 21u64;
    #[macro_export]
    pub const L0_OFFSET: u64 = 12u64;
    #[macro_export]
    pub const PT_ENTRY_NUM_BIT: u64 = 9u64;
}

crate::macro_const! {
    #[macro_export]
    pub const L3_PGSIZE: u64 = BIT64!(39);
    #[macro_export]
    pub const L2_PGSIZE: u64 = BIT64!(30);
    #[macro_export]
    pub const L1_PGSIZE: u64 = BIT64!(21);
    #[macro_export]
    pub const L0_PGSIZE: u64 = BIT64!(12);
    #[macro_export]

    pub const PT_ENTRY_NUM: u64 = BIT64!(9);
}

crate::macro_const! {
    #[macro_export]
    pub const PT_ENTRY_IDX_MASK: u64 = 0x1ff;
}

verus! {

pub spec fn spec_page_frame_bits() -> u64;

#[inline]
#[verifier(external_body)]
pub fn page_frame_bits() -> (ret: u64)
    ensures
        ret == spec_page_frame_bits(),
        48 <= spec_page_frame_bits() < 52,
{
    51
}

} // verus!
