use super::perm_s::*;
use super::*;

verus! {

#[verifier(opaque)]
pub open spec fn rmp_inv(rmp: &RmpMap) -> bool {
    &&& (forall|i: SPN| rmp.dom().contains(i) ==> #[trigger] rmp[i].inv())
}

pub open spec fn rmp_model_eq(rmp: &RmpMap, other: &RmpMap) -> bool {
    &&& (rmp_inv(other) ==> rmp_inv(rmp))
    &&& (forall|memid|
        (rmp_inv_sw(other, memid) ==> rmp_inv_sw(rmp, memid)))  // tODO: prove this
    &&& rmp.dom() === other.dom()
    &&& (forall|spn: SPN|
        rmp[spn].view().spec_validated() ==> #[trigger] rmp[spn] === #[trigger] other[spn])
    &&& (*rmp === rmp_hv_update(other, *rmp, MemID::Hv))
}

pub open spec fn rmp_reverse(rmp: &RmpMap, memid: MemID, gpn: GPN) -> SPN {
    choose|spn|
        {
            &&& (#[trigger] rmp[spn]).view().spec_gpn() === gpn
            &&& rmp.dom().contains(spn)
            &&& rmp[spn].view().spec_validated()
            &&& rmp[spn].view().spec_asid() === memid.to_asid()
        }
}

#[verifier(inline)]
pub open spec fn rmp_reverse_mem(rmp: &RmpMap, memid: MemID, gpmem: GPMem) -> SPMem {
    let spn = rmp_reverse(rmp, memid, gpmem.to_page());
    gpmem.convert(spn)
}

/*
    #[verifier(inline)]
    pub open spec fn rmp_reverse_addr(rmp: &RmpMap, memid: MemID, gpa: GPA) -> SPA {
        let spn = rmp_reverse(rmp, memid, gpa.to_page());
        gpa.convert(spn)
    }*/

pub open spec fn rmp_has_gpn(rmp: &RmpMap, gpn: GPN) -> bool {
    exists|spn|
        {
            &&& (#[trigger] rmp[spn]).view().spec_gpn() === gpn
            &&& #[trigger] rmp.dom().contains(spn)
            &&& rmp[spn].view().spec_validated()
        }
}

pub open spec fn rmp_has_gpn_memid(rmp: &RmpMap, gpn: GPN, memid: MemID) -> bool {
    exists|spn|
        {
            &&& (#[trigger] rmp[spn]).view().spec_gpn() === gpn
            &&& rmp.dom().contains(spn)
            &&& rmp[spn].view().spec_validated()
            &&& rmp[spn].view().spec_asid() === memid.to_asid()
        }
}

// To guarantee integrity, sm should validate GPA once.
// Checking double pvalidate error in rflag is not enough.
// To dynamically change share/private, verismo must track which gpa
// is validated and invalidated
pub open spec fn rmp_inv_sw(rmp: &RmpMap, memid: MemID) -> bool {
    forall|spn: SPN|
        {
            &&& #[trigger] rmp.dom().contains(spn)
            &&& (#[trigger] rmp[spn]).view().spec_validated()
            &&& rmp[spn].view().spec_asid() === memid.to_asid()
        } ==> (rmp_reverse(rmp, memid, rmp[spn].view().spec_gpn()) === spn)
}

// If memtype is sm_init, the gpn is only assigned to memid,
// If it is validated, hypervisor or other VMPLs cannot write to it.
pub open spec fn rmp_inv_memid_int(rmp: &RmpMap, memid: MemID) -> bool {
    forall|spn: SPN, vmpl: VMPL|
        {
            &&& rmp.dom().contains(spn)
            &&& memtype(memid, rmp[spn].view().spec_gpn()).is_sm_int()
            &&& vmpl.as_int() > memid.to_vmpl().as_int()
            &&& rmp[spn].view().spec_asid() === memid.to_asid()
        } ==> !#[trigger] rmp[spn].view().check_vmpl(vmpl, Perm::Write)
}

pub open spec fn rmp_hv_update(rmp: &RmpMap, newrmp: RmpMap, memid: MemID) -> RmpMap {
    RmpMap::new(
        |spn: SPN| rmp.dom().contains(spn),
        |spn: SPN| { rmp.spec_index(spn).rmpupdate(newrmp.spec_index(spn)).to_result() },
    )
}

} // verus!
