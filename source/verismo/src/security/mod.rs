use alloc::vec::Vec;

use crate::addr_e::*;
use crate::arch::addr_s::*;
use crate::arch::entities::VMPL;
use crate::debug::VPrintAtLevel;
use crate::global::*;
use crate::pgtable_e::va_to_pa;
use crate::ptr::*;
use crate::registers::*;
use crate::snp::cpu::VmsaPage;
use crate::snp::ghcb::*;
use crate::snp::SnpCoreSharedMem;
use crate::trusted_hacl::*;
use crate::tspec::*;
use crate::tspec_e::*;
use crate::vbox::*;
use crate::*;

mod mem;
mod monitor;
pub mod pcr;
pub mod secret;
pub use mem::*;
pub use monitor::*;
pub use secret::*;

verus! {

pub const USER_DATA_LEN: usize = 64;

pub const MAX_AUTHTAG_LEN: usize = 32;

pub const SNP_AEAD_AES_256_GCM: u8 = 1;

pub const MSG_HDR_VER: u8 = 1;

pub const SNP_GUEST_MSG_TYPE_REQ: u8 = 5;

pub const SNP_GUEST_MSG_TYPE_RESP: u8 = 6;

pub const SNP_ERR_REQ_RESP_MSG: u8 = 0xff;

pub const VERISMO_VMPCK_ID: u8 = 0;

} // verus!
verus! {

pub open spec fn is_richos_vmsa_box(vmsa: VBox<VmsaPage>) -> bool {
    &&& vmsa.snp().is_vmpl0_private()
    &&& vmsa.is_page()
    &&& vmsa@.vmpl.spec_eq(RICHOS_VMPL)
}

pub open spec fn richos_vmsa_invfn() -> spec_fn(Vec<Option<VBox<VmsaPage>>>) -> bool {
    |vec: Vec<Option<VBox<VmsaPage>>>|
        forall|i|
            0 <= i < vec@.len() ==> (vec[i].is_Some() ==> is_richos_vmsa_box(
                #[trigger] vec[i].get_Some_0(),
            ))
}

} // verus!
verismo_simple! {
    #[repr(C, align(1))]
    #[derive(Copy, VClone)]
    pub struct SecretsOSArea {
        msg_seqno_0: u32,
        msg_seqno_1: u32,
        msg_seqno_2: u32,
        msg_seqno_3: u32,
        ap_jump_table_pa: u64,
        reserved_1: Array<u8, 40>,
        guest_usage: Array<u8, 32>,
    }
}

verus! {

pub const MAX_SNP_MSG_SZ: u16 = 4000;

pub const MAX_SNP_MSG_SZ_USIZE: usize = MAX_SNP_MSG_SZ as usize;

} // verus!
verismo_simple! {
    type SnpGuestMsgPayload = Array<u8, MAX_SNP_MSG_SZ_USIZE>;
    #[repr(C, align(1))]
    #[derive(SpecGetter, SpecSetter)]
    pub struct SnpGuestMsg {
        #[def_offset]
        pub snphdr: SnpGuestMsgHdr,
        #[def_offset]
        pub payload: Array<u8, MAX_SNP_MSG_SZ_USIZE>,
    }
}

verismo_simple! {
    #[repr(C, align(1))]
    pub struct SnpReportReq {
        /* user data that should be included in the report */
        pub user_data: Array<u8_s, 64>,

        /* The vmpl level to be included in the report */
        pub vmpl: u32_t,

        /* Must be zero filled */
        pub reserved: Array<u8_t, 28>,
    }
}

verismo_simple! {
    type SnpReportResp = OnePage;

    pub struct SnpGuestChannel {
        pub req: VBox<SnpGuestMsg>,
        pub resp: VBox<SnpGuestMsg>,
    }

    impl SnpGuestChannel {
        pub open spec fn only_val_updated(&self, prev: Self) -> bool {
            &&& self.req.only_val_updated(prev.req)
            &&& self.resp.only_val_updated(prev.resp)
        }
    }
}

verismo_simple! {
    pub struct TrackedSecretsOSAreaPerms {
        pub perms: Tracked<SnpPointsTo<SecretsOSArea>>
    }
}

verus! {

proof fn proof_msg_hdr_size()
    ensures
        spec_size::<SnpGuestMsgHdr>() == AsNat!(0x60),
{
}

impl SnpGuestChannel {
    pub open spec fn wf(&self) -> bool {
        &&& self.req.is_shared_page()
        &&& self.resp.is_shared_page()
    }
}

} // verus!
