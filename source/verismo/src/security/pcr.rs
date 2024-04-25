use alloc::vec::Vec;

use super::secret::cal2_sha512;
use super::*;

pub type U256 = Array<u8_s, 32>;

verismo_simple! {
pub struct SHA256WithChain {
    pub val: [u8; 32],
    pub chain: Tracked<Seq<Seq<u8>>>,
}
}

verismo_simple! {
#[derive(SpecGetter, SpecSetter)]
pub struct ExtendPCRReq {
    #[def_offset]
    pub val: Array<u8, 64>,
    pub reserved: [u8; {0x1000 - 64}],
}
}

verus! {

pub open spec fn pcr_invfn() -> spec_fn(Vec<SHA512Type>) -> bool {
    |vec: Vec<SHA512Type>| vec.len() > 1 && forall|i| 0 < i < vec.len() ==> vec[i].wf()
}

} // verus!
verus! {

#[verifier(external_body)]
pub fn extend_pcr(
    index: usize,
    data: &Array<u8_s, USER_DATA_LEN>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
)
    requires
        data.wf(),
        old(cs).inv_stage_pcr(),
    ensures
        cs.inv_stage_pcr(),
        cs.only_lock_reg_coremode_updated(*old(cs), set![], set![spec_PCR_lockid()]),
{
    (new_strlit("extend_pcr"), index).leak_debug();
    let tracked pcr_lock = cs.lockperms.tracked_remove(spec_PCR_lockid());
    let (pcr_ptr, Tracked(mut pcr_perm), Tracked(mut pcr_lock)) = PCR().acquire(
        Tracked(pcr_lock),
        Tracked(&cs.snpcore.coreid),
    );
    assert(pcr_invfn()(pcr_perm@.get_value()));
    let mut pcr = pcr_ptr.take(Tracked(&mut pcr_perm));
    if pcr.len() < index {
        new_strlit("pcr.len() < index").leak_debug();
    } else if pcr.len() == index {
        pcr.push(cal_sha512(data));
    } else {
        let pcr_data = pcr[index];
        pcr.set(0, cal2_sha512(&pcr_data, data));
    }
    pcr_ptr.put(Tracked(&mut pcr_perm), pcr);
    PCR().release(Tracked(&mut pcr_lock), Tracked(pcr_perm), Tracked(&cs.snpcore.coreid));
    proof {
        cs.lockperms.tracked_insert(spec_PCR_lockid(), pcr_lock);
    }
}

#[inline]
pub fn attest_pcr(
    guest_channel: SnpGuestChannel,
    ghcb: GhcbHandle,
    secret: &SnpSecretsPageLayout,
    index: usize,
    report: VBox<OnePage>,
    Tracked(cs): Tracked<&mut SnpCoreSharedMem>,
) -> (ret: (VBox<OnePage>, SnpGuestChannel, GhcbHandle))
    requires
        guest_channel.wf(),
        ghcb.ghcb_wf(),
        secret.wf_mastersecret(),
        report.wf(),
        report.snp() === SwSnpMemAttr::spec_default(),
        old(cs).inv_stage_pcr(),
    ensures
        cs.inv_stage_pcr(),
        cs.only_lock_reg_coremode_updated(
            *old(cs),
            set![],
            set![spec_PCR_lockid(), spec_ALLOCATOR_lockid()],
        ),
        ret.0.wf(),
        ret.0.only_val_updated(report),
        ret.1.wf(),
        ret.1.only_val_updated(guest_channel),
        ret.2.ghcb_wf(),
        ret.2.only_val_updated(ghcb),
{
    let ghost cs1 = *cs;
    let tracked pcr_lock = cs.lockperms.tracked_remove(spec_PCR_lockid());
    let (pcr_ptr, Tracked(mut pcr_perm), Tracked(mut pcr_lock)) = PCR().acquire(
        Tracked(pcr_lock),
        Tracked(&cs.snpcore.coreid),
    );
    let pcr = pcr_ptr.borrow(Tracked(&pcr_perm));
    assert(pcr_invfn()(pcr_perm@.get_value()));
    if index >= pcr.len() {
        (new_strlit("PCR index not found:"), index).leak_debug();
        vc_terminate(SM_TERM_INVALID_PARAM, Tracked(&mut cs.snpcore));
    }
    let pcr_data = pcr[index].clone();
    PCR().release(Tracked(&mut pcr_lock), Tracked(pcr_perm), Tracked(&cs.snpcore.coreid));
    proof {
        cs.lockperms.tracked_insert(spec_PCR_lockid(), pcr_lock);
    }
    let ghost cs2 = *cs;
    let ret = guest_channel.attest(ghcb, secret, pcr_data, report, Tracked(cs));
    proof {
        cs1.lemma_update_prop(
            cs2,
            *cs,
            set![],
            set![spec_PCR_lockid()],
            set![],
            set![spec_ALLOCATOR_lockid()],
        );
        assert(set![spec_PCR_lockid()].union(set![spec_ALLOCATOR_lockid()])
            =~~= set![spec_PCR_lockid(), spec_ALLOCATOR_lockid()]);
    }
    ret
}

} // verus!
