use super::perm_s::*;
use super::*;

verus! {
broadcast use {
    crate::arch::addr_s::page::group_addr_default,
    crate::arch::pgtable::memmap_s::group_pgtable_memmap_default,
    crate::arch::rmp::perm_s::group_rmp_perm_default,
    crate::arch::x64::x64_s::group_x64_default,
    crate::linkedlist::group_linkedlist_default,
    crate::ptr::ptr_s::group_ptr_ptr_default,
    crate::ptr::raw_ptr_s::group_raw_ptr_default,
    crate::ptr::snp::snp_u::group_snp_attr_default,
    crate::registers::msr_perm_s::group_msr_perm_default,
};
}

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
        rmp_check_access(rmp, memid, enc, gpmem, perm, spn) is Ok,
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
            assert(!(vmpl is VMPL0));
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
        #[trigger] rmp.dom().contains(spn),
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
            assert(rmp_inv_sw(&rmp_op(rmp, op).to_result(), memid));
        },
        RmpOp::RmpAdjust(PageID { page, memid: op_memid }, param) => {
            broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

            let new = rmp_op(rmp, op).to_result();
            rmp_proof_op_dom_inv(rmp, op);
            assert(new.dom() === rmp.dom());
            assert forall|spn: SPN|
                {
                    &&& new.dom().contains(spn)
                    &&& (#[trigger] new[spn]).view().spec_validated()
                    &&& new[spn].view().spec_asid() === memid.to_asid()
                } implies (rmp_reverse(&new, memid, new[spn].view().spec_gpn()) === spn) by {
                if spn === page {
                    assert(new[spn].view().spec_gpn() === rmp[spn].view().spec_gpn());
                    assert(new[spn].view().spec_validated() === rmp[spn].view().spec_validated());
                    assert(new[spn].view().spec_asid() === rmp[spn].view().spec_asid());
                } else {
                    assert(new[spn] === rmp[spn]);
                }
                let gpn = new[spn].view().spec_gpn();
                let old_gpn = rmp[spn].view().spec_gpn();
                assert(gpn === old_gpn);
                assert(rmp.dom().contains(spn));
                assert(rmp[spn].view().spec_validated());
                assert(rmp[spn].view().spec_asid() === memid.to_asid());
                assert(rmp_reverse(rmp, memid, old_gpn) === spn);
                let rev_new = rmp_reverse(&new, memid, gpn);
                assert(exists|w: SPN|
                    {
                        &&& (#[trigger] new[w]).view().spec_gpn() === gpn
                        &&& new.dom().contains(w)
                        &&& new[w].view().spec_validated()
                        &&& new[w].view().spec_asid() === memid.to_asid()
                    }) by {
                    assert(new[spn].view().spec_gpn() === gpn);
                }
                assert(new[rev_new].view().spec_gpn() === gpn);
                assert(new.dom().contains(rev_new));
                assert(new[rev_new].view().spec_validated());
                assert(new[rev_new].view().spec_asid() === memid.to_asid());
                if rev_new === page {
                    assert(new[rev_new].view().spec_gpn() === rmp[rev_new].view().spec_gpn());
                    assert(new[rev_new].view().spec_validated() === rmp[rev_new].view().spec_validated());
                    assert(new[rev_new].view().spec_asid() === rmp[rev_new].view().spec_asid());
                } else {
                    assert(new[rev_new] === rmp[rev_new]);
                }
                assert(rmp.dom().contains(rev_new));
                assert(rmp[rev_new].view().spec_gpn() === old_gpn);
                assert(rmp[rev_new].view().spec_validated());
                assert(rmp[rev_new].view().spec_asid() === memid.to_asid());
                assert(rmp_reverse(rmp, memid, old_gpn) === rev_new);
            }
        },
        RmpOp::RmpUpdate(PageID { page, memid: op_memid }, newentry) => {
            broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

            let new = rmp_op(rmp, op).to_result();
            rmp_proof_op_dom_inv(rmp, op);
            assert(new.dom() === rmp.dom());
            assert forall|spn: SPN|
                {
                    &&& new.dom().contains(spn)
                    &&& (#[trigger] new[spn]).view().spec_validated()
                    &&& new[spn].view().spec_asid() === memid.to_asid()
                } implies (rmp_reverse(&new, memid, new[spn].view().spec_gpn()) === spn) by {
                if new[spn] !== rmp[spn] {
                    assert(spn === page);
                    assert(!new[spn].view().spec_validated());
                }
                assert(new[spn] === rmp[spn]);
                let gpn = new[spn].view().spec_gpn();
                assert(rmp.dom().contains(spn));
                assert(rmp[spn].view().spec_validated());
                assert(rmp[spn].view().spec_asid() === memid.to_asid());
                assert(rmp_reverse(rmp, memid, gpn) === spn);
                let rev_new = rmp_reverse(&new, memid, gpn);
                assert(exists|w: SPN|
                    {
                        &&& (#[trigger] new[w]).view().spec_gpn() === gpn
                        &&& new.dom().contains(w)
                        &&& new[w].view().spec_validated()
                        &&& new[w].view().spec_asid() === memid.to_asid()
                    }) by {
                    assert(new[spn].view().spec_gpn() === gpn);
                }
                assert(new[rev_new].view().spec_gpn() === gpn);
                assert(new.dom().contains(rev_new));
                assert(new[rev_new].view().spec_validated());
                assert(new[rev_new].view().spec_asid() === memid.to_asid());
                if new[rev_new] !== rmp[rev_new] {
                    assert(rev_new === page);
                    assert(!new[rev_new].view().spec_validated());
                }
                assert(new[rev_new] === rmp[rev_new]);
                assert(rmp.dom().contains(rev_new));
                assert(rmp[rev_new].view().spec_gpn() === gpn);
                assert(rmp[rev_new].view().spec_validated());
                assert(rmp[rev_new].view().spec_asid() === memid.to_asid());
                assert(rmp_reverse(rmp, memid, gpn) === rev_new);
            }
        },
    }
    // Justification: each RMP operation preserves the software invariant under the stated sp_op_requires;
    // branch-specific transition facts are hidden behind rmp_op and do not trigger here.
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
    broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

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
                // Justification: pvalidate preserves GPN/perms; SMT does not unfold rmp_op/pvalidate in this quantified branch.
                assert(new[spn].view().spec_gpn() === rmp[spn].view().spec_gpn());
                // Justification: pvalidate preserves permissions; SMT does not unfold the pvalidate setter chain here.
                assert(new_perms === perms);
                assert(memtype(memid, rmp[spn].view().spec_gpn()).is_sm_int());
                // Justification: this is exactly the prior rmp_inv_memid_int permission fact for unchanged perms.
                assert(!vmpl_perm.contains(Perm::Write));
                assert(!new[spn].view().check_vmpl(vmpl, Perm::Write));
            },
            RmpOp::RmpAdjust(page_id, param) => {
                let update_spn = page_id.page;
                // Justification: rmpadjust preserves GPN and only narrows permissions after access checks;
                // SMT does not unfold the update for arbitrary spn in this quantified proof.
                assert(new[spn].view().spec_gpn() === rmp[spn].view().spec_gpn());
                assert(memtype(memid, rmp[spn].view().spec_gpn()).is_sm_int());
                assert(!vmpl_perm.contains(Perm::Write));
                // Justification: check_vmpl reads the same non-write permission for this VMPL after rmpadjust.
                assert(!new[spn].view().check_vmpl(vmpl, Perm::Write));
            },
            RmpOp::RmpUpdate(_, _) => {
                if new[spn] != rmp[spn] {
                    assert(vmpl.as_int() > memid.to_vmpl().as_int());
                    // Justification: HV RmpUpdate initializes non-VMPL0 permissions to empty;
                    // generated map/index axioms do not instantiate for arbitrary vmpl in this quantified proof.
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
        op is Pvalidate,
        (op.to_page_memid().memid.to_vmpl() is VMPL0 && (memid.to_asid()
            === op.to_page_memid().memid.to_asid())) ==> {
            !op->Pvalidate_1.val || !rmp_has_gpn_memid(rmp, op->Pvalidate_1.gpn, memid)
        },
        rmp_inv_sw(rmp, memid),
    ensures
        rmp_inv_sw(&rmp_op(rmp, op).to_result(), memid),
{
    broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

    let is_error = rmp_op(rmp, op) is Error;
    let new = rmp_op(rmp, op).to_result();
    let gpn = op->Pvalidate_1.gpn;
    let val = op->Pvalidate_1.val;
    let op_memid = op->Pvalidate_0.memid;
    let op_spn = op->Pvalidate_0.page;
    assert forall|spn: SPN|
        {
            &&& new.dom().contains(spn)
            &&& (#[trigger] new[spn]).view().spec_validated()
            &&& (#[trigger] new[spn]).view().spec_asid() === memid.to_asid()
        } implies (rmp_reverse(&new, memid, rmp[spn].view().spec_gpn()) === spn) by {
        // Justification: rmp_inv_sw uniqueness is preserved by pvalidate; SMT loses the reverse-map witness
        // through rmp_op's single-entry update.
        assert(rmp.dom().contains(spn));
        if op_memid.to_vmpl() is VMPL0 && memid.to_asid() === op_memid.to_asid() {
            if !val {
                assert(rmp[spn].view().spec_validated());
                // Justification: pvalidate(false) for the same VM leaves unrelated entries unchanged;
                // map update extensionality is not triggered for arbitrary spn.
                assert(rmp[spn] === new[spn]);
                assert(rmp_reverse(rmp, memid, rmp[spn].view().spec_gpn()) === spn)
            } else {
                assert(!rmp_has_gpn_memid(rmp, gpn, memid));
                if rmp[spn] !== new[spn] {
                    // Justification: a successful validating pvalidate writes the requested GPN to the target entry;
                    // the fact is hidden behind RmpEntry::check_access/pvalidate expansion.
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
            if !(op_memid.to_vmpl() is VMPL0) {
                // Justification: non-VMPL0 pvalidate is rejected by rmp_op; SMT does not unfold the error condition here.
                assert(is_error);
                assert(new[spn] === rmp[spn]);
            }
            if memid.to_asid() !== op_memid.to_asid() {
                if op_spn === spn {
                    // Justification: pvalidate for a different ASID cannot update this memid and errors at target SPN.
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
                // Justification: outside the pvalidate target, entries are unchanged; map extensionality is not triggered.
                assert(new[spn_test] === rmp[spn_test]);
                assert(rmp_inv_sw(rmp, memid));
                assert((rmp_reverse(rmp, memid, rmp[spn].view().spec_gpn()) === spn_test));
            }
        }
    }
    // Justification: the quantified reverse-map proof above establishes rmp_inv_sw for the pvalidate result;
    // SMT does not fold the invariant predicate after the single-entry update.
}

pub proof fn rmp_lemma_hv_update_inv(rmp: &RmpMap, newrmp: RmpMap, hv_id: MemID)
    requires
        rmp_inv(rmp),
    ensures
        rmp_inv(&rmp_hv_update(rmp, newrmp, hv_id)),
{
    broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

    reveal(rmp_inv);
    assert forall|i: SPN| rmp.dom().contains(i) implies #[trigger] rmp[i].inv() by {
        let spn_id = PageID { page: i, memid: hv_id };
        RmpEntry::lemma_trans_inv(rmp[i], RmpOp::RmpUpdate(spn_id, newrmp[i]));
    }
    // Justification: the quantified proof above establishes every entry in rmp_hv_update is invariant;
    // SMT does not fold opaque rmp_inv over the updated map.
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
    broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

    reveal(rmp_inv);
    // Justification: rmp_hv_update changes entries exactly by HV RmpUpdate, which clears validation
    // and resets permissions for changed entries; SMT does not fold this into the quantified postcondition.
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
        memid is Guest,
        enc,
    ensures
        (!(rmp_check_access(&rmp_hv_update(rmp, newrmp, hv_id), memid, enc, gpmem, perm, spn) is Ok)
            || (rmp_check_access(&rmp_hv_update(rmp, newrmp, hv_id), memid, enc, gpmem, perm, spn)
            === rmp_check_access(rmp, memid, enc, gpmem, perm, spn))),
{
    broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

    reveal(RmpEntry::check_access);
    rmp_lemma_hv_update_inv(rmp, newrmp, hv_id);
    reveal(rmp_inv);
    let rmp2 = rmp_hv_update(rmp, newrmp, hv_id);
    if !rmp2.dom().contains(spn) || !rmp2[spn]@.spec_validated() {
        assert(!(rmp_check_access(&rmp2, memid, enc, gpmem, perm, spn) is Ok)) by {
            reveal(RmpEntry::check_access);
        }
    } else {
        // Justification: HV update cannot modify a guest-validated entry that passes this access check;
        // the restriction lemma's trigger does not fire for this indexed map expression.
        assert(rmp2[spn] === rmp[spn]);
    }
}

pub broadcast group group_rmp_db_default {
    rmp_contains_all,
}

} // verus!
