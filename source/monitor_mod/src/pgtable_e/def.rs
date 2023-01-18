use super::*;
use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::debug::VPrintAtLevel;
use crate::global::*;
use crate::registers::{AnyRegTrait, RegisterPerm, RegisterPermValue};
use crate::snp::SnpCoreSharedMem;
use crate::*;

verus! {
pub type PageTable = Array<u64_s, 512>;

pub const PAT_RESET_VAL: u64 = 0x7040600070406;

pub const PAGE_TABLE_LEVELS: u8 = 4;

#[vbit_struct(PTE, u64)]
pub struct SpecPTE {
    #[vbits(0, 0)]
    pub present: u64,
    #[vbits(1, 1)]
    pub write: u64,
    #[vbits(2, 2)]
    pub supervisor: u64,
    #[vbits(3, 3)]
    pub pwt: u64,
    #[vbits(4, 4)]
    pub pcd: u64,
    #[vbits(5, 5)]
    pub accessed: u64,
    #[vbits(6, 6)]
    pub dirty: u64,
    #[vbits(7, 7)]
    pub psize: u64,
    #[vbits(8, 8)]
    pub global: u64,
    #[vbits(12, 12)]
    pub bit12: u64,
    #[vbits(51, 51)]
    pub encrypted: u64,
    #[vbits(12, 50)]
    pub page: u64,
    #[vbits(63, 63)]
    pub nx: u64,
}

// Private perms to prevent
pub struct PtePerm {
    pub lvl: nat,
    pub val: PTE, // current lvl, entry value
    pub range: (int, nat),
    pub perm: Option<SnpPointsTo<PageTable>>, // memory perms for next table
}

pub type PtePerms = Map<(nat, int), PtePerm>;
}

verus! {
pub closed spec fn static_cr3_value() -> int;
pub open spec fn top_lvl_idx() -> (nat, int) {
    (PAGE_TABLE_LEVELS as nat, 0)
}
pub trait PtePermsTrait {
    spec fn pte(&self, vaddr: int) -> Option<PtePerm>;

    spec fn pde(&self, vaddr: int) -> Option<PtePerm>;

    spec fn pdpe(&self, vaddr: int) -> Option<PtePerm>;

    spec fn pml4e(&self, vaddr: int) -> Option<PtePerm>;

    spec fn entry(&self, vaddr: int, lvl: nat) -> Option<PtePerm>;
}
}

verismo_simple! {
pub struct TrackedPTEPerms {
    pub perms: Tracked<PtePerms>
}
}
