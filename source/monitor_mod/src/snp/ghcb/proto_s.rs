use super::*;

verus! {
pub const GHCB_VERSION_1: u16 = 1;

#[is_variant]
#[derive(SpecIntEnum, Copy, Clone)]
pub enum PageOps {
    Private = 1,
    Shared = 2,
    Smash = 3,
    Unsmash = 4,
}

impl WellFormed for PageOps {
    open spec fn wf(&self) -> bool {
        true
    }
}

impl IsConstant for PageOps {
    open spec fn is_constant(&self) -> bool {
        true
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        true
    }
}
}

verus! {
pub const GHCB_MSR_SEV_INFO_REQ: u64 = 0x002;

pub const GHCB_MSR_SEV_INFO_RES: u64 = 0x001;

pub const GHCB_MSR_REGISTER_GHCB_REQ: u64 = 0x012;

pub const GHCB_MSR_REGISTER_GHCB_RES: u64 = 0x013;

pub const GHCB_SNP_PAGE_STATE_CHANGE_REQ: u64 = 0x0014;

pub const GHCB_SNP_PAGE_STATE_CHANGE_RESP: u64 = 0x0015;

pub const GHCB_MSR_TERMINATE_REQ: u64 = 0x100;

pub const GHCB_MSR_INFO_MASK: u64 = 0xfff;

pub const GHCB_DEFAULT_USAGE: u32 = 0;

pub const GHCB_VTL_RETURN_USAGE: u32 = 2;

// GHCB exit code
pub const SVM_EXIT_VMGEXIT: u64 = 0x403;

pub const SVM_EXIT_MSR: u64 = 0x07c;

pub const SVM_EXIT_VMMCALL: u64 = 0x081;

pub const SVM_EXIT_PAGE_STATE_CHANGE: u64 = 0x80000010;

pub const SVM_EXIT_SNP_GUEST_REQUEST: u64 = 0x80000011;

#[derive(SpecIntEnum)]
pub enum SVMExitCode {
    VmgExit = 0x403,
    MSR = 0x07c,
    VmmCall = 0x081,
    MaskInt = 0xfff,
    PageStateChange = 0x80000010,
    SnpGuestRequest = 0x80000011,
}
}

#[macro_export]
macro_rules! SVM_EVTINJ_VEC_MASK {
    ($x: expr) => {
        ($x & 0xff)
    };
}

verus! {
pub const SVM_EVTINJ_VEC_X86_TRAP_GP: u64 = 13;

pub const SVM_EVTINJ_VEC_X86_TRAP_UD: u64 = 6;
}

#[macro_export]
macro_rules! SVM_EVTINJ_TYPE_MASK {
    ($x: expr) => {
        ($x & 0b111_0000_0000)
    };
}

verus! {
pub const SVM_EVTINJ_TYPE_EXEPT: u64 = 0b11_0000_0000u64;

pub const SVM_EVTINJ_VALID_BIT: u64 = 31;

// VeriSMo termination constants
/// 15
pub const SM_SEV_TERM_SET: u64 = 0x3;
/// 0
pub const SM_TERM_GENERAL: u64 = 0;
/// 1
pub const SM_TERM_NOT_VMPL0: u64 = 1;
/// 2
pub const SM_TERM_UNHANDLED_VC: u64 = 2;
/// 3
pub const SM_TERM_PSC_ERROR: u64 = 3;
/// 4
pub const SM_TERM_SET_PAGE_ERROR: u64 = 4;
/// 5
pub const SM_TERM_NO_GHCB: u64 = 5;
/// 6
pub const SM_TERM_GHCB_RESP_INVALID: u64 = 6;
/// 7
pub const SM_TERM_INVALID_PARAM: u64 = 7;
/// 8
pub const SM_TERM_PVALIDATE: u64 = 8;

/// 8
pub const SM_TERM_MEM: u64 = 0x11;

pub const SM_EVERCRYPT_EXIT: u64 = 0xa;

pub const SM_TERM_TIMEOUT: u64 = 0xb;

pub const SM_TERM_VMM_ERR: u64 = 0xc;

pub const SM_TERM_GHCB_EXCEPTION: u64 = 0xd;

pub const SM_TERM_UNSUPPORTED: u64 = 0xe;

pub const SM_TERM_RICHOS: u64 = 0xf;

pub const SM_TERM_PERMS: u64 = 0x10;
}

macro_const! {
#[verifier::publish]
pub const SUBCODE_OFFSET: u64 = 0x8u64;
}

verus! {
    pub open spec fn spec_valid_page_state_change(ppage: u64, npages: nat) -> bool {
        &&& ppage + npages <= 0x100_0000_0000
    }

    pub open spec fn ensure_page_perm_change_state(
        prev_memperm: SnpPointsToRaw, memperm: SnpPointsToRaw, ppage: int, op: PageOps) -> bool {
        &&& memperm@.snp().ensures_rmpupdate(prev_memperm@.snp(), op.is_Shared(), op.is_Unsmash())
        &&& (memperm)@.wf_range(prev_memperm@.range())
        &&& ppage == (memperm)@.ppage()
    }

    pub open spec fn requires_pages_perms(page_perms: Map<int, SnpPointsToRaw>, ppage: int, npages: nat) -> bool {
        &&& wf_page_range(page_perms, ppage, npages)
    }

    pub open spec fn ensure_pages_perm_change_state(
        prev_pageperms: Map<int, SnpPointsToRaw>, page_perms: Map<int, SnpPointsToRaw>, ppage: int, npages: nat, op: PageOps) -> bool {
        &&& prev_pageperms.dom() =~~= page_perms.dom()
        &&& forall |i| ppage <= i < (ppage + npages) ==>
            page_perms.contains_key(i)
        &&& forall |i| ppage <= i < (ppage + npages) ==>
            ensure_page_perm_change_state(prev_pageperms[i], #[trigger]page_perms[i], i, op)
    }

    impl GHCBProto
    {
        /// only works on 4k page
        pub open spec fn spec_msr_page_state_req(page: usize, op: PageOps) -> u64
        {
            let opu64 = op.as_int() as u64;
            GHCB_SNP_PAGE_STATE_CHANGE_REQ |
            (page as u64 & 0xfff_ffff_ffff) << 12 |
            (opu64 << 52)
        }

        pub open spec fn spec_exit_value(reason_code: u64) -> u64 {
            GHCB_MSR_TERMINATE_REQ | (SM_SEV_TERM_SET << 12u64) | (reason_code << 16u64)
        }
    }
}
