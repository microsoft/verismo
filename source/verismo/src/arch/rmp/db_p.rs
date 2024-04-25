use super::perm_s::*;
use super::*;

verus! {

pub proof fn rmp_proof_check_access_rmp_has_gpn_memid(
    rmp: &RmpMap,
    memid: MemID,
    enc: bool,
    gpmem: GPMem,
    perm: Perm,
    spn: SPN,
)
    requires
        rmp_check_access(rmp, memid, enc, gpmem, perm, spn).is_Ok(),
        enc,
    ensures
        rmp_has_gpn_memid(rmp, gpmem.to_page(), memid),
{
    reveal(RmpEntry::check_access);
}

pub proof fn rmp_lemma_model_eq_inv(rmp: &RmpMap, other: &RmpMap, memid: MemID)
    requires
        rmp_model_eq(rmp, other),
        rmp_inv(other),
    ensures
        rmp_inv(rmp),
        rmp_inv_memid_int(other, memid) ==> rmp_inv_memid_int(rmp, memid),
        rmp_inv_sw(other, memid) ==> rmp_inv_sw(rmp, memid),
{
    if rmp_inv_memid_int(other, memid) {
        assert forall|spn: SPN, vmpl: VMPL|
            {
                &&& rmp.dom().contains(spn)
                &&& memtype(memid, rmp[spn].view().spec_gpn()).is_sm_int()
                &&& vmpl.as_int() > memid.to_vmpl().as_int()
                &&& rmp[spn].view().spec_asid() === memid.to_asid()
            } implies !#[trigger] rmp[spn].view().check_vmpl(vmpl, Perm::Write) by {
            assert(!vmpl.is_VMPL0());
            rmp_lemma_hv_update_restrict(&other, *rmp, MemID::Hv);
            assert(*rmp === rmp_hv_update(other, *rmp, MemID::Hv));
            if rmp[spn] !== other[spn] {
                assert(rmp[spn].view().spec_perms() === rmp_perm_init());
                assert(rmp[spn].view().spec_perms().index(vmpl) === PagePerm::empty());
                assert(!rmp[spn].view().spec_perms().index(vmpl).contains(Perm::Write));
            } else {
                assert(!other[spn].view().check_vmpl(vmpl, Perm::Write));
            }
        }
    }
}

#[verifier(external_body)]
pub broadcast proof fn rmp_contains_all(rmp: &RmpMap, spn: SPN)
    ensures
        rmp.dom().contains(spn),
{
}

pub proof fn rmp_proof_op_dom_inv(rmp: &RmpMap, op: RmpOp<SysPhy>)
    ensures
        rmp_op(rmp, op).to_result().dom() === rmp.dom(),
{
    assert(rmp_op(rmp, op).to_result().dom() =~~= (rmp.dom()));
}

pub proof fn rmp_proof_op_inv(rmp: &RmpMap, op: RmpOp<SysPhy>)
    requires
        rmp_inv(rmp),
    ensures
        rmp_inv(&rmp_op(rmp, op).to_result()),
{
    reveal(rmp_inv);
    let spn = op.to_page_memid().page;
    let new = rmp_op(rmp, op).to_result();
    rmp_proof_op_dom_inv(rmp, op);
    if rmp.dom().contains(spn) {
        assert forall|i: SPN| new.dom().contains(i) implies #[trigger] new[i].inv() by {
            assert(rmp[i].inv());
            RmpEntry::lemma_trans_inv(rmp[spn], op);
        }
    }
}

pub proof fn rmp_proof_inv_sw(rmp: &RmpMap, op: RmpOp<SysPhy>, memid: MemID)
    requires
        rmp_inv_sw(rmp, memid),
        op.to_page_memid().memid.is_sm(memid) ==> op.sp_op_requires(
            rmp,
        ),
//rmp.sw_requires(op, memid),

    ensures
        rmp_inv_sw(&rmp_op(rmp, op).to_result(), memid),
{
    match op {
        RmpOp::Pvalidate(_, _) => {
            rmp_lemma_pvalidate_sw_inv(rmp, op, memid);
        },
        RmpOp::RmpAdjust(_, _) => {},
        RmpOp::RmpUpdate(_, _) => {},
    }
}

/// TODO: function body check has been running for 2 seconds
pub proof fn rmp_proof_inv_memid_int(rmp: &RmpMap, op: RmpOp<SysPhy>, memid: MemID)
    requires
        rmp_inv_memid_int(rmp, memid),
        rmp_inv(rmp),
        op.to_page_memid().memid.is_sm(memid) ==> op.sp_op_requires(rmp),
    ensures
        rmp_inv_memid_int(&rmp_op(rmp, op).to_result(), memid),
{
    reveal(rmp_inv);
    let new = rmp_op(rmp, op).to_result();
    rmp_proof_op_dom_inv(rmp, op);
    assert(new.dom() === rmp.dom());
    assert forall|spn: SPN, vmpl: VMPL|
        {
            &&& new.dom().contains(spn)
            &&& memtype(memid, new[spn].view().spec_gpn()).is_sm_int()
            &&& vmpl.as_int() > memid.to_vmpl().as_int()
            &&& new[spn].view().spec_asid() === memid.to_asid()
        } implies !#[trigger] new[spn].view().check_vmpl(vmpl, Perm::Write) by {
        assert(rmp[spn].inv());
        let new_perms = new[spn].view().spec_perms();
        let perms = rmp[spn].view().spec_perms();
        let new_vmpl_perm = new_perms[vmpl];
        let vmpl_perm = perms[vmpl];
        match op {
            RmpOp::Pvalidate(_, _) => {
                assert(new[spn].view().spec_gpn() === rmp[spn].view().spec_gpn());
                assert(new_perms === perms);
                assert(memtype(memid, rmp[spn].view().spec_gpn()).is_sm_int());
                assert(!vmpl_perm.contains(Perm::Write));
                assert(!new[spn].view().check_vmpl(vmpl, Perm::Write));
            },
            RmpOp::RmpAdjust(page_id, param) => {
                let update_spn = page_id.page;
                assert(new[spn].view().spec_gpn() === rmp[spn].view().spec_gpn());
                assert(memtype(memid, rmp[spn].view().spec_gpn()).is_sm_int());
                assert(!vmpl_perm.contains(Perm::Write));
                assert(!new[spn].view().check_vmpl(vmpl, Perm::Write));
            },
            RmpOp::RmpUpdate(_, _) => {
                if new[spn] != rmp[spn] {
                    assert(vmpl.as_int() > memid.to_vmpl().as_int());
                    assert(new_vmpl_perm === PagePerm::empty());
                    assert(!new_vmpl_perm.contains(Perm::Write));
                } else {
                    assert(!rmp[spn].view().check_vmpl(vmpl, Perm::Write));
                }
                assert(!new[spn].view().check_vmpl(vmpl, Perm::Write));
            },
        }
    }
}

pub proof fn rmp_lemma_pvalidate_sw_inv(rmp: &RmpMap, op: RmpOp<SysPhy>, memid: MemID)
    requires
        op.is_Pvalidate(),
        (op.to_page_memid().memid.to_vmpl().is_VMPL0() && (memid.to_asid()
            === op.to_page_memid().memid.to_asid())) ==> {
            !op.get_Pvalidate_1().val || !rmp_has_gpn_memid(rmp, op.get_Pvalidate_1().gpn, memid)
        },
        rmp_inv_sw(rmp, memid),
    ensures
        rmp_inv_sw(&rmp_op(rmp, op).to_result(), memid),
{
    let is_error = rmp_op(rmp, op).is_Error();
    let new = rmp_op(rmp, op).to_result();
    let gpn = op.get_Pvalidate_1().gpn;
    let val = op.get_Pvalidate_1().val;
    let op_memid = op.get_Pvalidate_0().memid;
    let op_spn = op.get_Pvalidate_0().page;
    assert forall|spn: SPN|
        {
            &&& new.dom().contains(spn)
            &&& (#[trigger] new[spn]).view().spec_validated()
            &&& (#[trigger] new[spn]).view().spec_asid() === memid.to_asid()
        } implies (rmp_reverse(&new, memid, rmp[spn].view().spec_gpn()) === spn) by {
        assert(rmp.dom().contains(spn));
        if op_memid.to_vmpl().is_VMPL0() && memid.to_asid() === op_memid.to_asid() {
            if !val {
                assert(rmp[spn].view().spec_validated());
                assert(rmp[spn] === new[spn]);
                assert(rmp_reverse(rmp, memid, rmp[spn].view().spec_gpn()) === spn)
            } else {
                assert(!rmp_has_gpn_memid(rmp, gpn, memid));
                if rmp[spn] !== new[spn] {
                    assert(new[spn].view().spec_gpn() === gpn) by {
                        reveal(RmpEntry::check_access);
                    }
                    assert forall|spn_test: SPN|
                        {
                            &&& spn_test !== spn
                            &&& #[trigger] rmp.dom().contains(spn_test)
                            &&& new[spn_test].view().spec_asid() === memid.to_asid()
                        } implies ((#[trigger] new[spn_test]).view().spec_gpn() !== gpn)
                        || !new[spn_test].view().spec_validated() by {
                        assert(new[spn_test] === rmp[spn_test]);
                        assert(!rmp_has_gpn_memid(rmp, gpn, memid));
                    }
                }
            }
        } else {
            if !op_memid.to_vmpl().is_VMPL0() {
                assert(is_error);
                assert(new[spn] === rmp[spn]);
            }
            if memid.to_asid() !== op_memid.to_asid() {
                if op_spn === spn {
                    assert(is_error);
                }
                assert(new[spn] === rmp[spn]);
            }
            assert(rmp_reverse(rmp, memid, rmp[spn].view().spec_gpn()) === spn);
            assert forall|spn_test: SPN|
                {
                    &&& #[trigger] rmp.dom().contains(spn_test)
                    &&& new[spn_test].view().spec_asid() === memid.to_asid()
                    &&& ((#[trigger] new[spn_test]).view().spec_gpn()
                        === rmp[spn].view().spec_gpn())
                    &&& new[spn_test].view().spec_validated()
                } implies spn_test === spn by {
                assert(new[spn_test] === rmp[spn_test]);
                assert(rmp_inv_sw(rmp, memid));
                assert((rmp_reverse(rmp, memid, rmp[spn].view().spec_gpn()) === spn_test));
            }
        }
    }
}

pub proof fn rmp_lemma_hv_update_inv(rmp: &RmpMap, newrmp: RmpMap, hv_id: MemID)
    requires
        rmp_inv(rmp),
    ensures
        rmp_inv(&rmp_hv_update(rmp, newrmp, hv_id)),
{
    reveal(rmp_inv);
    assert forall|i: SPN| rmp.dom().contains(i) implies #[trigger] rmp[i].inv() by {
        let spn_id = PageID { page: i, memid: hv_id };
        RmpEntry::lemma_trans_inv(rmp[i], RmpOp::RmpUpdate(spn_id, newrmp[i]));
    }
}

pub proof fn rmp_lemma_hv_update_restrict(rmp: &RmpMap, newrmp: RmpMap, hv_id: MemID)
    requires
        rmp_inv(rmp),
    ensures
        forall|i|
            (rmp.dom().contains(i) && (#[trigger] rmp_hv_update(rmp, newrmp, hv_id)[i] !== rmp[i]))
                ==> (!rmp_hv_update(rmp, newrmp, hv_id)[i]@.spec_validated() && rmp_hv_update(
                rmp,
                newrmp,
                hv_id,
            )[i]@.spec_perms() === rmp_perm_init()),
{
    reveal(rmp_inv);
}

pub proof fn rmp_lemma_hv_update_restrict_at(
    rmp: &RmpMap,
    hv_id: MemID,
    newrmp: RmpMap,
    memid: MemID,
    enc: bool,
    gpmem: GPMem,
    perm: Perm,
    spn: SPN,
)
    requires
        rmp_inv(rmp),
        memid.is_Guest(),
        enc,
    ensures
        (!rmp_check_access(&rmp_hv_update(rmp, newrmp, hv_id), memid, enc, gpmem, perm, spn).is_Ok()
            || (rmp_check_access(&rmp_hv_update(rmp, newrmp, hv_id), memid, enc, gpmem, perm, spn)
            === rmp_check_access(rmp, memid, enc, gpmem, perm, spn))),
{
    reveal(RmpEntry::check_access);
    rmp_lemma_hv_update_inv(rmp, newrmp, hv_id);
    reveal(rmp_inv);
    let rmp2 = rmp_hv_update(rmp, newrmp, hv_id);
    if !rmp2.dom().contains(spn) || !rmp2[spn]@.spec_validated() {
        assert(!rmp_check_access(&rmp2, memid, enc, gpmem, perm, spn).is_Ok()) by {
            reveal(RmpEntry::check_access);
        }
    } else {
        assert(rmp2[spn] === rmp[spn]);
    }
}

} // verus!
