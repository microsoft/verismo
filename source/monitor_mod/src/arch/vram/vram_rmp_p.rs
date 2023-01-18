use super::*;

verus! {
impl VRamDB {
    pub proof fn lemma_rmpop_enc_byte_Ginv(&self, sysmap: SysMap, memop: MemOp<GuestPhy>, memid: MemID, gpa: GPA)
    requires
        self.inv(),
        memop.is_RmpOp(),
        self.inv_sw(memid),
        memop.get_RmpOp_0().inv(),
        //self.op(sysmap, memop).is_Ok(),
        memop.to_memid().is_sm(memid) ==> self.gpmemop_requires(memop, sysmap),
    ensures
        (self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa).is_Some() && self.get_enc_byte_ok(memid, gpa).is_Some()) ==>
            self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa),
        (self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa).is_Some() && !self.get_enc_byte_ok(memid, gpa).is_Some()) ==>
        (memop.to_page() === gpa.to_page() && memop.is_RmpOp() && memop.get_RmpOp_0().is_Pvalidate() &&
        memop.get_RmpOp_0().get_Pvalidate_1().val)
    {
        reveal(VRamDB::op);
        let other = &self.op(sysmap, memop).to_result();
        assert(self.spec_sram() === other.spec_sram());
        let gpn = gpa.to_page();
        let rmp = self.spec_rmp();
        let rmpop = memop.get_RmpOp_0();
        let new_rmp = other.spec_rmp();
        let spn = rmp_reverse(&rmp, memid, gpn);
        let new_spn = rmp_reverse(&new_rmp, memid, gpn);
        if other.get_enc_byte_ok(memid, gpa).is_Some() && self.get_enc_byte_ok(memid, gpa).is_Some() {
            assert(rmp_has_gpn_memid(&rmp, gpn, memid));
            assert(rmp_has_gpn_memid(&new_rmp, gpn, memid));
            assert(rmp[spn].view().spec_validated());
            assert(new_rmp[spn].view().spec_validated());
            assert(rmp[spn].view().spec_gpn() === new_rmp[new_spn].view().spec_gpn());
            assert(spn === new_spn);
        } else if other.get_enc_byte_ok(memid, gpa).is_Some() {
            assert(rmpop.is_Pvalidate());
            assert(rmpop.get_Pvalidate_1().val);
            assert(rmp_has_gpn_memid(&new_rmp, gpn, memid));
            assert(new_rmp[new_spn].view().spec_validated());
            assert(new_rmp[new_spn].view().spec_gpn() === gpn);
            assert(memop.to_page() === gpn);
        }
    }

    /// Rmpop.Rinv: when other memid execute RmpOp
    pub proof fn lemma_rmpop_enc_byte_vm_Rinv(&self, sysmap: SysMap, memop: MemOp<GuestPhy>, memid: MemID, gpa: GPA) -> (ok: bool)
    requires
        self.inv(),
        memop.is_RmpOp(),
        self.inv_sw(memid),
        memid.is_vmpl0(),
        memop.is_valid(),
        memop.to_memid().is_sm(memid) ==> self.gpmemop_requires(memop, sysmap),
        memop.to_memid() != memid,
    ensures
        ok == (self.op(sysmap, memop).is_Ok() && self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa).is_Some()),
        ok ==>
        self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa),
    {
        reveal(VRamDB::op);
        let new = &self.op(sysmap, memop).to_result();
        assert(self.spec_sram() === new.spec_sram());
        let gpn = gpa.to_page();
        let rmp = self.spec_rmp();
        let new_rmp = new.spec_rmp();
        let ok = self.op(sysmap, memop).is_Ok() && new.get_enc_byte_ok(memid, gpa).is_Some();
        if ok {
            let spn = rmp_reverse(&rmp, memid, gpn);
            let new_spn = rmp_reverse(&new_rmp, memid, gpn);
            assert(rmp_has_gpn_memid(&new_rmp, gpn, memid));
            assert(new_rmp[spn].view().spec_validated());
            assert(rmp[spn].view().spec_validated());
            assert(rmp_has_gpn_memid(&rmp, gpn, memid));
            assert(self.get_enc_byte_ok(memid, gpa).is_Some());
            assert(rmp[spn].view().spec_gpn() === new_rmp[new_spn].view().spec_gpn());
            assert(spn === new_spn);
        }
        ok
    }

    pub proof fn lemma_rmpop_effect_unchange(&self, sysmap: SysMap, memop: MemOp<GuestPhy>, memid: MemID, gpa: GPA)
    requires
        self.inv(),
        self.inv_sw(memid),
        self.inv_memid_int(memid),
        memop.is_RmpOp(),
        memop.get_RmpOp_0().inv(),
        self.op(sysmap, memop).is_Ok(),
        memop.is_valid(),
        memop.to_page() !== gpa.to_page(),
        memid.is_vmpl0(),
        memop.to_memid().is_sm(memid) ==> self.gpmemop_requires(memop, sysmap),
        //memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1(),
    ensures
        self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa).is_Some() ==>
            (self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa))
    {
        let new = &self.op(sysmap, memop).to_result();
        reveal(VRamDB::op);
        assert(self.spec_sram() === new.spec_sram());
        assert(new.inv_sw(memid)) by {
            self.proof_op_inv_sw(sysmap, memop, memid);
        }
        let encbyte = self.get_enc_byte_ok(memid, gpa);
        let new_encbyte = new.get_enc_byte_ok(memid, gpa);
        let gpn = gpa.to_page();
        let op_gpn = memop.to_page();
        let spn = rmp_reverse(&self.spec_rmp(),memid, gpn);
        let new_spn = rmp_reverse(&new.spec_rmp(),memid, gpn);
        let op_spn = rmp_reverse(&self.spec_rmp(),memid, op_gpn);
        if !rmp_has_gpn_memid(&self.spec_rmp(),gpn, memid) {
            assert(encbyte.is_None());
            if rmp_has_gpn_memid(&new.spec_rmp(),gpn, memid) {
                assert(new.spec_rmp()[new_spn].view().spec_validated());
                assert(new.spec_rmp()[new_spn].view().spec_asid() === memid.to_asid());
                assert(memop.is_PValidate());
                assert(self.spec_rmp()[new_spn].view().spec_asid() === memid.to_asid());
                assert(!self.spec_rmp()[new_spn].view().spec_validated());
                assert(new.spec_rmp()[new_spn].view().spec_gpn() === op_gpn) by {
                    reveal(RmpEntry::check_access);
                }
                assert(new.spec_rmp()[new_spn].view().spec_gpn() === gpn);
            }
            assert(!rmp_has_gpn_memid(&new.spec_rmp(),gpn, memid))
        }
        if new_encbyte.is_Some() {
            assert(rmp_has_gpn_memid(&new.spec_rmp(),gpn, memid));
            assert(rmp_has_gpn_memid(&self.spec_rmp(),gpn, memid));
            assert(new.spec_rmp()[new_spn].view().spec_gpn() === gpn);
            assert(self.spec_rmp()[spn].view().spec_gpn() === gpn);
            assert(rmp_reverse(&new.spec_rmp(),memid, gpn) === new_spn);
            assert(rmp_reverse(&self.spec_rmp(),memid, gpn) === new_spn);
            assert(new_spn === spn);
        }
    }
}
}
