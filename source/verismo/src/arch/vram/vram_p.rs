use super::*;
use crate::arch::ramdb::ram_s::*;
use crate::arch::rmp::perm_s::Perm;

verus! {

impl VRamDB {
    pub proof fn proof_rmp_check_access_rmp_has_gpn_memid(
        &self,
        op: MemOp<GuestPhy>,
        sysmap: SysMap,
    )
        requires
            op.is_Read() || op.is_Write(),
            self.op(sysmap, op).is_Ok(),
            op.to_enc(),
        ensures
            rmp_has_gpn_memid(&self.rmp, op.to_mem().to_page(), op.to_memid()),
    {
        reveal(VRamDB::op);
        let spn = sysmap.translate(op.to_mem().to_page()).get_Some_0();
        if op.is_Write() {
            rmp_proof_check_access_rmp_has_gpn_memid(
                &self.rmp,
                op.to_memid(),
                op.to_enc(),
                op.to_mem(),
                Perm::Write,
                spn,
            );
        }
        if op.is_Read() {
            rmp_proof_check_access_rmp_has_gpn_memid(
                &self.rmp,
                op.to_memid(),
                op.to_enc(),
                op.to_mem(),
                Perm::Read,
                spn,
            );
        }
    }

    pub proof fn lemma_read_no_change(&self, op: MemOp<GuestPhy>, sysmap: SysMap)
        requires
            op.is_Read(),
            op.is_valid(),
        ensures
            &self.op(sysmap, op).to_result() === self,
    {
        reveal(VRamDB::op);
    }

    pub proof fn lemma_error_no_change(&self, op: MemOp<GuestPhy>, sysmap: SysMap)
        requires
            self.op(sysmap, op).is_Error(),
            op.is_valid(),
        ensures
            &self.op(sysmap, op).to_result() === self,
    {
        reveal(VRamDB::op);
    }

    pub proof fn lemma_constant_gpn_to_spn_when_enc(&self, op: MemOp<GuestPhy>, sysmap: SysMap)
        requires
            self.inv(),
            self.inv_sw(op.to_memid()),
            op.is_valid(),
            op.is_Read() || op.is_Write(),
            self.op(sysmap, op).is_Ok() || self.op(sysmap, op).get_Error_1().is_RmpOp(),
            op.is_Read() ==> op.get_Read_1(),
            op.is_Write() ==> op.get_Write_1(),
        ensures
            sysmap.translate(op.to_mem().to_page()).is_Some(),
            rmp_has_gpn_memid(&self.spec_rmp(), op.to_mem().to_page(), op.to_memid()),
            rmp_reverse(&self.spec_rmp(), op.to_memid(), op.to_mem().to_page())
                === sysmap.translate(op.to_mem().to_page()).get_Some_0(),
    {
        reveal(VRamDB::op);
        reveal(RmpEntry::check_access);
        reveal(rmp_inv);
        let spn = sysmap.translate(op.to_mem().to_page());
        assert(spn.is_Some()) by {
            if spn.is_None() {
                if op.is_Read() {
                    assert(self.op(sysmap, op).is_Error());
                }
                if op.is_Write() {
                    assert(self.op(sysmap, op).is_Error());
                }
            }
        }
        let spn = spn.get_Some_0();
        assert(self.spec_rmp()[spn].view().spec_validated());
        assert(rmp_reverse(&self.spec_rmp(), op.to_memid(), self.spec_rmp()[spn].view().spec_gpn())
            === spn) by {
            assert(self.inv_sw(op.to_memid()));
        }
    }

    pub proof fn proof_read_enc_byte_to_bytes(&self, memid: MemID, gpmem: GPMem, i: int)
        requires
            0 <= i < gpmem.len(),
            gpmem.is_valid(),
        ensures
            self.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }).is_Some()
                === self.get_enc_byte_ok(memid, gpmem[i]).is_Some(),
            self.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }).is_Some()
                ==> self.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }).get_Some_0()[i]
                === self.get_enc_byte_ok(memid, gpmem[i]).get_Some_0(),
    {
        gpmem.proof_same_page();
    }

    /// TODO: function body check has been running for 2 seconds
    pub proof fn lemma_write_enc_bytes_effect_same_read(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpmem: GPMem,
    )
        requires
            self.inv(),
            memop.is_Write(),
            memop.is_valid(),
            gpmem.is_valid(),
            gpmem.len() > 0,
            self.inv_sw(memid),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            gpmem === memop.to_mem(),
            memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1(),
        ensures
            (other.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }).is_Some()
                && memop.get_Write_1()) ==> (other.get_enc_bytes_ok(
                AddrMemID { memid, range: gpmem },
            ).get_Some_0() === memop.get_Write_2()),
            (other.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }).is_Some()
                && !memop.get_Write_1()) ==> {
                other.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }) === self.get_enc_bytes_ok(
                    AddrMemID { memid, range: gpmem },
                )
            },
            self.rmp.dom() === self.op(sysmap, memop).to_result().rmp.dom(),
    {
        let gpmem_id = AddrMemID { memid, range: gpmem };
        let read1 = self.get_enc_bytes_ok(gpmem_id);
        let read2 = other.get_enc_bytes_ok(gpmem_id);
        let w_enc = memop.get_Write_1();
        //self.lemma_inv_dom(other, sysmap, memop);
        reveal(VRamDB::op);
        assert(read2.is_Some() === read1.is_Some());
        if gpmem === memop.to_mem() && read2.is_Some() && w_enc {
            assert forall|i| 0 <= i < gpmem.len() implies read2.get_Some_0()[i]
                === #[trigger] memop.get_Write_2()[i] by {
                self.lemma_write_effect_in_range(other, sysmap, memop, memid, gpmem[i]);
                other.proof_read_enc_byte_to_bytes(memid, gpmem, i);
            }
            assert(memop.get_Write_2() =~~= (read2.get_Some_0()));
        }
        if gpmem === memop.to_mem() && read2.is_Some() && !w_enc {
            assert forall|i| 0 <= i < gpmem.len() implies read2.get_Some_0()[i]
                === #[trigger] read1.get_Some_0()[i] by {
                if 0 <= i < gpmem.len() {
                    self.lemma_write_effect_in_range(other, sysmap, memop, memid, gpmem[i]);
                    other.proof_read_enc_byte_to_bytes(memid, gpmem, i);
                }
            }
            assert(read1.get_Some_0() =~~= (read2.get_Some_0()));
        }
    }

    pub proof fn lemma_write_enc_bytes_effect_disjoint_read(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpmem: GPMem,
    )
        requires
            self.inv(),
            memid.is_vmpl0(),
            memop.is_valid(),
            memop.is_Write(),
            gpmem.is_valid(),
            gpmem.len() > 0,
            self.inv_sw(memid),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            gpmem.disjoint(
                memop.to_mem(),
            ),
    //memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1(),

        ensures
            other.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }) === self.get_enc_bytes_ok(
                AddrMemID { memid, range: gpmem },
            ),
            self.rmp.dom() === self.op(sysmap, memop).to_result().rmp.dom(),
    {
        let gpmem_id = AddrMemID { memid, range: gpmem };
        let read1 = self.get_enc_bytes_ok(gpmem_id);
        let read2 = other.get_enc_bytes_ok(gpmem_id);
        let w_enc = memop.get_Write_1();
        //self.lemma_inv_dom(other, sysmap, memop);
        reveal(VRamDB::op);
        assert(read2.is_Some() === read1.is_Some());
        if read2.is_Some() {
            assert forall|i| 0 <= i < gpmem.len() implies read2.get_Some_0()[i]
                === read1.get_Some_0()[i] by {
                if 0 <= i < gpmem.len() {
                    other.proof_read_enc_byte_to_bytes(memid, gpmem, i);
                    self.proof_read_enc_byte_to_bytes(memid, gpmem, i);
                    if memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1() {
                        self.lemma_write_effect_out_range(other, sysmap, memop, memid, gpmem[i]);
                    } else {
                        self.lemma_write_byte_other_vm(other, sysmap, memop, memid, gpmem[i]);
                    }
                }
            }
            assert(read1.get_Some_0() =~~= (read2.get_Some_0()));
        }
    }

    pub proof fn lemma_write_bytes_effect_by_other_vm_or_shared(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpmem: GPMem,
    )
        requires
            self.inv(),
            memid.is_vmpl0(),
            memop.is_valid(),
            memop.is_Write(),
            gpmem.is_valid(),
            gpmem.len() > 0,
            self.inv_sw(memid),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            (memop.to_memid().to_asid() !== memid.to_asid() && memop.get_Write_1())
                || !memop.get_Write_1(),
        ensures
            other.get_enc_bytes_ok(AddrMemID { memid, range: gpmem }) === self.get_enc_bytes_ok(
                AddrMemID { memid, range: gpmem },
            ),
            self.rmp.dom() === self.op(sysmap, memop).to_result().rmp.dom(),
    {
        let gpmem_id = AddrMemID { memid, range: gpmem };
        let read1 = self.get_enc_bytes_ok(gpmem_id);
        let read2 = other.get_enc_bytes_ok(gpmem_id);
        let w_enc = memop.get_Write_1();
        //self.lemma_inv_dom(other, sysmap, memop);
        reveal(VRamDB::op);
        assert(read2.is_Some() === read1.is_Some());
        if read2.is_Some() {
            assert forall|i| 0 <= i < gpmem.len() implies read2.get_Some_0()[i]
                === read1.get_Some_0()[i] by {
                if 0 <= i < gpmem.len() {
                    other.proof_read_enc_byte_to_bytes(memid, gpmem, i);
                    self.proof_read_enc_byte_to_bytes(memid, gpmem, i);
                    if w_enc {
                        self.lemma_write_byte_other_vm(other, sysmap, memop, memid, gpmem[i]);
                    } else {
                        self.lemma_write_shared_effect(other, sysmap, memop, memid, gpmem[i]);
                    }
                }
            }
            assert(read1.get_Some_0() =~~= (read2.get_Some_0()));
        }
    }

    pub proof fn lemma_write_sm_int_Rinv(
        &self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            self.inv(),
            self.inv_sw(memid),
            self.inv_memid_int(memid),
            gpa.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            memid.is_vmpl0(),
            !memop.to_memid().is_sm(memid),
            memtype(memid, gpa.to_page()).is_sm_int(),
        ensures
            self.op(sysmap, memop).to_result().get_enc_byte_ok(memid, gpa).is_Some() ==> self.op(
                sysmap,
                memop,
            ).to_result().get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa),
    {
        let new = self.op(sysmap, memop).to_result();
        if self.op(sysmap, memop).is_Ok() {
            if memop.to_mem().contains(gpa) {
                self.lemma_write_sm_int_ok(memid, memop, sysmap);
                self.lemma_write_byte_othervm_or_shared(&new, sysmap, memop, memid, gpa);
            } else {
                self.lemma_write_effect_out_range(&new, sysmap, memop, memid, gpa);
            }
        }
        self.lemma_op_err_Ginv(sysmap, memop);
    }

    pub proof fn lemma_write_byte_othervm_or_shared(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            self.inv(),
            gpa.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            memid.is_vmpl0(),
            self.inv_sw(memid),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            (memop.to_memid().to_asid() !== memid.to_asid() && memop.get_Write_1())
                || !memop.get_Write_1(),
        ensures
            other.get_enc_byte_ok(memid, gpa).is_Some() ==> other.get_enc_byte_ok(memid, gpa)
                === self.get_enc_byte_ok(memid, gpa),
    {
        let w_enc = memop.get_Write_1();
        if w_enc {
            self.lemma_write_byte_other_vm(other, sysmap, memop, memid, gpa);
        } else {
            self.lemma_write_shared_effect(other, sysmap, memop, memid, gpa);
        }
    }

    pub proof fn lemma_write_byte_other_vm(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            memid.is_vmpl0(),
            self.inv(),
            self.inv_sw(memid),
            memop.is_valid(),
            memop.is_Write(),
            gpa.is_valid(),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            (memop.to_memid().to_asid() !== memid.to_asid()),
        ensures
            other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa),
    {
        reveal(VRamDB::op);
        assert(other.get_enc_byte_ok(memid, gpa).is_Some() === self.get_enc_byte_ok(
            memid,
            gpa,
        ).is_Some());
        let w_asid = if memop.get_Write_1() {
            memop.to_memid().to_asid()
        } else {
            ASID_FOR_HV!()
        };
        if self.get_enc_byte_ok(memid, gpa).is_Some() {
            let rspn = rmp_reverse(&self.spec_rmp(), memid, gpa.to_page());
            let rspa = gpa.convert(rspn);
            assert(self.spec_rmp()[rspn].inv()) by {
                reveal(rmp_inv);
            }
            assert(self.spec_rmp()[rspn].view().spec_asid() === memid.to_asid());
            assert(self.spec_rmp()[rspn].view().spec_validated());
            let wspmem = sysmap.translate_addr_seq(memop.to_mem());
            assert(w_asid !== memid.to_asid());
            assert(wspmem.to_page() !== rspn) by {
                reveal(RmpEntry::check_access);
            }
            assert(!memrange_contains_block(wspmem, idx(rspa))) by {
                let wspn = wspmem.to_page();
                let base_addr = wspn.to_addr().as_int();
                assert(base_addr <= wspmem.first().as_int() < base_addr + PAGE_SIZE!());
                assert(base_addr <= wspmem.last().as_int() < base_addr + PAGE_SIZE!());
                // The following proofs are unstable. Keep those assertions to help solver.
                assert(!(rspn =~= wspn));
                assert(base_addr == wspn.as_int() * PAGE_SIZE!());
                let rbase_addr = rspn.to_addr().as_int();
                assert(rbase_addr == rspn.as_int() * PAGE_SIZE!());
                assert(rbase_addr <= rspa.as_int() < rbase_addr + PAGE_SIZE!());
                assert((rbase_addr <= base_addr - PAGE_SIZE!()) || (rbase_addr >= base_addr
                    + PAGE_SIZE!()));
            }
            self.spec_sram().lemma_write_unchange_byte_any_enc(
                w_asid,
                wspmem,
                memop.get_Write_2(),
                memid.to_asid(),
                rspa,
            );
        }
    }

    pub proof fn lemma_write_effect_change_other_vm_enc(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
        rsysmap: SysMap,
        renc: bool,
    )
        requires
            self.inv(),
            self.inv_sw(memid),
            gpa.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            (memop.to_memid().to_asid() !== memid.to_asid() && memop.get_Write_1()),
        ensures
    //other.read_bytes(AddrMemID{range: gpa, memid}, renc, rsysmap) === self.read_bytes(AddrMemID{range: gpa, memid}, renc, rsysmap),

            other.read_bytes(
                AddrMemID { range: SpecMem::from_range(gpa, 1), memid },
                renc,
                rsysmap,
            ).is_Ok() ==> (other.get_byte(memid, gpa, renc, rsysmap) === self.get_byte(
                memid,
                gpa,
                renc,
                rsysmap,
            )),
            other.get_enc_byte_ok(memid, gpa).is_Some() ==> other.get_enc_byte_ok(memid, gpa)
                === self.get_enc_byte_ok(memid, gpa),
    {
        reveal(VRamDB::op);
        reveal(VRamDB::op_write);
        reveal(RmpEntry::check_access);
        reveal(rmp_inv);
        let rmp = self.spec_rmp();
        assert(rmp === other.spec_rmp());
        let rspn = rmp_reverse(&rmp, memid, gpa.to_page());
        let rspa = gpa.convert(rspn);
        let AddrMemID { range, memid: w_memid } = memop.to_addr_memid();
        let data = memop.get_Write_2();
        let w_enc = memop.get_Write_1();
        let wspmem = sysmap.translate_addr_seq(range);
        let rspa_by_sysmap = rsysmap.translate_addr(gpa);
        assert(rmp === other.spec_rmp());
        assert(rmp[wspmem.to_page()].view().spec_asid() === memop.to_memid().to_asid());
        assert(rmp[wspmem.to_page()].view().spec_validated());
        assert(rmp[wspmem.to_page()].view().spec_assigned());
        assert(rmp[wspmem.to_page()].inv());
        if other.read_bytes(
            AddrMemID { range: SpecMem::from_range(gpa, 1), memid },
            renc,
            rsysmap,
        ).is_Ok() {
            assume(other.get_byte(memid, gpa, renc, rsysmap) === self.get_byte(
                memid,
                gpa,
                renc,
                rsysmap,
            ));
        }
        assume(other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa));
    }

    pub proof fn lemma_write_shared_effect(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            self.inv(),
            self.inv_sw(memid),
            gpa.is_valid(),
            memid.is_vmpl0(),
            memop.is_valid(),
            memop.is_Write(),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            !memop.get_Write_1(),
        ensures
    //other.get_enc_byte_ok(memid, gpa).is_Some() ==>

            other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa),
            (memop.to_mem().contains(gpa) && !other.get_enc_byte_ok(memid, gpa).is_Some()) ==> (
            other.get_byte(memop.to_memid(), gpa, memop.get_Write_1(), sysmap).get_Some_0()
                === memop.get_Write_2()[gpa.value() - memop.to_mem().first().value()]),
    {
        if let MemOp::Write(gpa_id, w_enc, bytes) = memop {
            let gpmem_id = memop.to_addr_memid();
            if gpmem_id.range.contains(gpa) {
                self.lemma_write_effect_in_range(other, sysmap, memop, memid, gpa);
                if other.get_enc_byte_ok(memid, gpa).is_Some() {
                    assert(other.get_enc_byte_ok(memid, gpa).get_Some_0() === self.get_enc_byte_ok(
                        memid,
                        gpa,
                    ).get_Some_0());
                } else {
                    assert(other.get_byte(memid, gpa, false, sysmap).get_Some_0()
                        === memop.get_Write_2()[gpa.value() - memop.to_mem().first().value()]);
                }
            } else {
                self.lemma_write_effect_out_range(other, sysmap, memop, memid, gpa);
            }
        }
    }

    pub proof fn lemma_write_effect_in_range(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            self.inv(),
            self.inv_sw(memid),
            gpa.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            memop.to_mem().contains(gpa),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1(),
        ensures
            other.get_byte(memid, gpa, false, sysmap).is_Some(),
            (other.get_enc_byte_ok(memid, gpa).is_Some() && memop.get_Write_1()) ==> (
            other.get_enc_byte_ok(memid, gpa).get_Some_0() === memop.get_Write_2()[gpa.value()
                - memop.to_mem().first().value()]),
            !(other.get_enc_byte_ok(memid, gpa).is_Some() && memop.get_Write_1()) ==> (
            other.get_byte(memop.to_memid(), gpa, memop.get_Write_1(), sysmap).get_Some_0()
                === memop.get_Write_2()[gpa.value() - memop.to_mem().first().value()]),
            (!other.get_enc_byte_ok(memid, gpa).is_Some() && !memop.get_Write_1()) ==> {
                other.get_byte(memid, gpa, false, sysmap).get_Some_0()
                    === memop.get_Write_2()[gpa.value() - memop.to_mem().first().value()]
            },
            !memop.get_Write_1() ==> {
                other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa)
            },
    {
        reveal(VRamDB::op);
        reveal(VRamDB::op_write);
        let rmp = self.spec_rmp();
        assert(rmp === other.spec_rmp());
        let rspn = rmp_reverse(&rmp, memid, gpa.to_page());
        let rspa = gpa.convert(rspn);
        assert(rspn =~= rspa.to_page());
        let AddrMemID { range, memid: w_memid } = memop.to_addr_memid();
        let data = memop.get_Write_2();
        let w_enc = memop.get_Write_1();
        let wspmem = sysmap.translate_addr_seq(range);
        assert(gpa.to_page() === range.to_page());
        reveal(RmpEntry::check_access);
        reveal(rmp_inv);
        assert(rmp[wspmem.to_page()].inv());
        if other.get_enc_byte_ok(memid, gpa).is_Some() && w_enc {
            assert(rmp[rspn].inv());
            assert(w_memid.to_asid() === memid.to_asid());
            assert(wspmem.contains(rspa)) by {
                assert(wspmem === rmp_reverse_mem(&rmp, w_memid, range));
                assert(range.to_page() === gpa.to_page());
                assert(wspmem.to_page() === rspa.to_page());
            }
            assert(self.get_enc_byte_ok(memid, gpa).is_Some());
            self.spec_sram().lemma_write_change_byte(memid.to_asid(), wspmem, data, rspa);
        } else {
            let w_asid = if w_enc {
                w_memid.to_asid()
            } else {
                ASID_FOR_HV!()
            };
            let rspa_by_sysmap = sysmap.translate_addr(gpa);
            assert(rspa_by_sysmap.is_Some());
            let rspa_by_sysmap = rspa_by_sysmap.get_Some_0();
            let read_byte_sysmap = other.get_byte(w_memid, gpa, w_enc, sysmap);
            assert(read_byte_sysmap.is_Some());
            if !w_enc {
                let read_byte = other.get_byte(memid, gpa, false, sysmap);
                assert(read_byte.is_Some());
                if other.get_enc_byte_ok(memid, gpa).is_Some() {
                    assert(rmp[rspn].inv());
                    assert(!rmp[wspmem.to_page()].view().spec_assigned());
                    assert(rmp[rspn].view().spec_validated());
                    assert(wspmem.to_page() !== rspn);
                    //self.spec_sram().lemma_write_unchange_byte_any_enc(w_asid, wspmem, data, memid.to_asid(), rspa);
                    //assert(other.get_enc_byte_ok(memid, gpa).get_Some_0() === self.get_enc_byte_ok(memid, gpa).get_Some_0());
                }
            }
            if wspmem.to_page() !== rspn {
                assert(0 <= rspa.as_int() - rspn.as_int() * (PAGE_SIZE as int) < (
                PAGE_SIZE as int));
                self.spec_sram().lemma_write_unchange_byte_any_enc(
                    w_asid,
                    wspmem,
                    data,
                    memid.to_asid(),
                    rspa,
                );
            }
            assert(other.spec_sram() === self.spec_sram().write_raw(w_asid, wspmem, data));
            self.spec_sram().lemma_write_change_byte(w_asid, wspmem, data, rspa_by_sysmap);
            assert(other.spec_sram().read_one_byte(w_asid, rspa_by_sysmap)
                === data[rspa_by_sysmap.value() - wspmem.first().value()]);
            assert(read_byte_sysmap.get_Some_0() === data[rspa_by_sysmap.value()
                - wspmem.first().value()]);
        }
    }

    pub proof fn lemma_write_effect_out_range(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            self.inv(),
            self.inv_sw(memid),
            memid.is_vmpl0(),
            gpa.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            !memop.to_mem().contains(gpa),
        ensures
            (other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa)),
    {
        if memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1() {
            self.lemma_write_effect_out_range_same_vm(other, sysmap, memop, memid, gpa);
        } else {
            self.lemma_write_byte_other_vm(other, sysmap, memop, memid, gpa);
        }
    }

    pub proof fn lemma_write_effect_out_range_same_vm(
        &self,
        other: &Self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        memid: MemID,
        gpa: GPA,
    )
        requires
            self.inv(),
            self.inv_sw(memid),
            memop.is_valid(),
            memop.is_Write(),
            self.op(sysmap, memop).is_Ok(),
            other === &self.op(sysmap, memop).to_result(),
            !memop.to_mem().contains(gpa),
            memop.to_memid().to_asid() === memid.to_asid() || !memop.get_Write_1(),
        ensures
            (other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa)),
    {
        reveal(VRamDB::op);
        reveal(VRamDB::op_write);
        let rmp = self.spec_rmp();
        assert(rmp === other.spec_rmp());
        let w_enc = memop.get_Write_1();
        let w_gpmem = memop.to_mem();
        let w_memid = memop.to_memid();
        let data = memop.get_Write_2();
        let wspmem = sysmap.translate_addr_seq(w_gpmem);
        wspmem.proof_same_page();
        if self.get_enc_byte_ok(memid, gpa).is_Some() {
            assert(rmp_has_gpn_memid(&rmp, gpa.to_page(), memid));
            let rspn = rmp_reverse(&rmp, memid, gpa.to_page());
            let rspa = gpa.convert(rspn);
            assert(rspa.to_page().value() == rspn.value());
            assert(rspa.to_page() =~= rspn);
            reveal(RmpEntry::check_access);
            assert(rmp[rspn].view().spec_validated());
            if w_enc {
                assert(rmp[wspmem.to_page()].view().spec_gpn() === w_gpmem.to_page());
                assert(rmp[rspa.to_page()].view().spec_gpn() === gpa.to_page());
                assert(rmp[wspmem.to_page()].view().spec_asid() === w_memid.to_asid());
                assert(rmp[rspa.to_page()].view().spec_asid() === memid.to_asid());
                assert(wspmem === rmp_reverse_mem(&rmp, w_memid, w_gpmem));
                if wspmem.to_page() === rspa.to_page() {
                    assert(!wspmem.contains(rspa));
                    assert(memid.to_asid() === w_memid.to_asid());
                    self.spec_sram().lemma_write_unchange_byte(memid.to_asid(), wspmem, data, rspa);
                } else {
                    self.spec_sram().lemma_write_unchange_byte_any_enc(
                        w_memid.to_asid(),
                        wspmem,
                        data,
                        memid.to_asid(),
                        rspa,
                    );
                }
                assert(other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa));
            } else {
                assert(!rmp[wspmem.to_page()].view().spec_validated()) by {
                    assert(!rmp[wspmem.to_page()].view().spec_assigned());
                    assert(rmp[wspmem.to_page()].inv()) by {
                        reveal(rmp_inv);
                    }
                }
                assert(wspmem.to_page() !== rspa.to_page());
                self.spec_sram().lemma_write_unchange_byte_any_enc(
                    w_memid.to_asid(),
                    wspmem,
                    data,
                    memid.to_asid(),
                    rspa,
                );
                assume(other.get_enc_byte_ok(memid, gpa) === self.get_enc_byte_ok(memid, gpa));
            }
        } else {
            assert(self.get_enc_byte_ok(memid, gpa).is_None());
        }
    }

    pub proof fn proof_op_inv(&self, sysmap: SysMap, memop: MemOp<GuestPhy>)
        requires
            self.inv(),
            memop.is_valid(),
            sysmap.is_valid(),
        ensures
            self.op(sysmap, memop).to_result().inv(),
    {
        reveal(VRamDB::inv);
        reveal(VRamDB::op);
        reveal(VRamDB::op_read);
        reveal(VRamDB::op_write);
        reveal(VRamDB::rmp_op);
        //reveal(RamDB::write_raw);
        let new = self.op(sysmap, memop).to_result();
        match memop {
            MemOp::RmpOp(rmpop) => {
                let spn = sysmap.translate(rmpop.get_gpn());
                if spn.is_Some() {
                    rmp_proof_op_dom_inv(&self.spec_rmp(), rmpop.set_spn(spn.get_Some_0()));
                    rmp_proof_op_inv(&self.spec_rmp(), rmpop.set_spn(spn.get_Some_0()));
                }
            },
            MemOp::Write(gpa_id, enc, data) => {
                let use_asid = if enc {
                    gpa_id.memid.to_asid()
                } else {
                    ASID_FOR_HV!()
                };
                if self.op(sysmap, memop).is_Ok() {
                    let spa = sysmap.translate_addr_seq(memop.to_mem());
                    self.spec_sram().lemma_write_inv(use_asid, spa, data);
                    assert(new.inv());
                }
            },
            _ => {},
        }
        let new = self.op(sysmap, memop).to_result();
    }

    pub proof fn proof_op_inv_sw(&self, sysmap: SysMap, memop: MemOp<GuestPhy>, memid: MemID)
        requires
            self.inv(),
            self.inv_sw(memid),
            self.inv_memid_int(memid),
            memop.is_valid(),
            memop.to_memid().is_sm(memid) ==> self.gpmemop_requires(memop, sysmap),
        ensures
            self.op(sysmap, memop).to_result().inv(),
            self.op(sysmap, memop).to_result().inv_sw(memid),
            self.op(sysmap, memop).to_result().inv_memid_int(memid),
    {
        reveal(VRamDB::inv);
        reveal(VRamDB::op);
        reveal(VRamDB::op_read);
        reveal(VRamDB::op_write);
        reveal(VRamDB::rmp_op);
        //reveal(RamDB::write_raw);
        self.proof_op_inv(sysmap, memop);
        match memop {
            MemOp::RmpOp(rmpop) => {
                let spn = sysmap.translate(rmpop.get_gpn());
                if spn.is_Some() {
                    rmp_proof_inv_sw(&self.spec_rmp(), rmpop.set_spn(spn.get_Some_0()), memid);
                    rmp_proof_inv_memid_int(
                        &self.spec_rmp(),
                        rmpop.set_spn(spn.get_Some_0()),
                        memid,
                    );
                }
            },
            _ => {},
        }
    }

    pub proof fn lemma_op_err_Ginv(&self, sysmap: SysMap, memop: MemOp<GuestPhy>)
        requires
            memop.is_valid(),
        ensures
            !self.op(sysmap, memop).is_Ok() ==> self.op(sysmap, memop).to_result() === *self,
            self.op(sysmap, memop).to_result() !== *self ==> self.op(sysmap, memop).is_Ok(),
    {
        reveal(VRamDB::op);
        reveal(VRamDB::op_read);
        reveal(VRamDB::op_write);
        reveal(VRamDB::rmp_op);
    }

    pub proof fn lemma_write_read_consistant(
        &self,
        sysmap: SysMap,
        memop: MemOp<GuestPhy>,
        rgpa_id: GPAMemID,
        enc: bool,
    )
        requires
            memop.is_valid(),
            memop.is_Write(),
            memop.to_mem() === rgpa_id.range,  // same gpa + memid
            memop.to_memid() === rgpa_id.memid,  // same gpa + memid
            memop.get_Write_1() === enc,  // same enc
            self.op(sysmap, memop).is_Ok(),
        ensures
            memop.get_Write_2() === self.op(sysmap, memop).to_result().get_bytes(
                rgpa_id,
                enc,
                sysmap,
            ),
    {
        reveal(VRamDB::op);
        reveal(VRamDB::op_write);
        let data = memop.get_Write_2();
        let new_vram = self.op(sysmap, memop).to_result();
        let gpmem = memop.to_mem();
        let memid = memop.to_memid();
        let spa = sysmap.translate_addr_seq(gpmem);
        assert(spa.len() === gpmem.len());
        let use_asid = if enc {
            memid.to_asid()
        } else {
            ASID_FOR_HV!()
        };
        self.spec_sram().proof_read_write(use_asid, spa, data);
    }

    pub proof fn lemma_read_op_enc_bytes_ok(&self, sysmap: SysMap, gpa_id: GPAMemID, enc: bool)
        requires
            enc,
            gpa_id.range.is_valid(),
            self.inv_sw(gpa_id.memid),
            self.op(sysmap, MemOp::Read(gpa_id, enc)).is_Ok(),
        ensures
            self.get_enc_bytes_ok(gpa_id).is_Some(),
            self.get_enc_bytes_ok(gpa_id).get_Some_0() === self.read_bytes(
                gpa_id,
                enc,
                sysmap,
            ).to_result(),
            sysmap.translate(gpa_id.range.to_page()).is_Some(),
            sysmap.translate(gpa_id.range.to_page()).get_Some_0() === rmp_reverse(
                &self.spec_rmp(),
                gpa_id.memid,
                gpa_id.range.to_page(),
            ),
    {
        reveal(VRamDB::op);
        self.lemma_read_enc_byte_ok(sysmap, gpa_id, enc);
    }

    pub proof fn lemma_read_enc_byte_ok(&self, sysmap: SysMap, gpa_id: GPAMemID, enc: bool)
        requires
            enc,
            gpa_id.range.is_valid(),
            self.inv_sw(gpa_id.memid),
            self.read_bytes(gpa_id, enc, sysmap).is_Ok(),
        ensures
            self.get_enc_bytes_ok(gpa_id).is_Some(),
            self.get_enc_bytes_ok(gpa_id).get_Some_0() === self.read_bytes(
                gpa_id,
                enc,
                sysmap,
            ).to_result(),
            sysmap.translate(gpa_id.range.to_page()).is_Some(),
            sysmap.translate(gpa_id.range.to_page()).get_Some_0() =~= rmp_reverse(
                &self.spec_rmp(),
                gpa_id.memid,
                gpa_id.range.to_page(),
            ),
    {
        let rmp = self.spec_rmp();
        let AddrMemID { range: gpmem, memid } = gpa_id;
        let gpn = gpmem.to_page();
        let spmem = rmp_reverse_mem(&rmp, memid, gpmem);
        assert(sysmap.translate(gpn).is_Some());
        assert(sysmap.translate_addr_seq(gpmem) === spmem) by {
            assert(self.inv_sw(gpa_id.memid));
            reveal(RmpEntry::check_access);
        }
        assert(rmp_has_gpn_memid(&rmp, gpn, memid)) by {
            reveal(RmpEntry::check_access);
        }
    }

    pub proof fn lemma_read_diff_sysmap(
        &self,
        sysmap1: SysMap,
        sysmap2: SysMap,
        gpa_id: GPAMemID,
        enc: bool,
    )
        requires
            enc,
            gpa_id.range.is_valid(),
            rmp_inv_sw(&self.rmp, gpa_id.memid),
        ensures
            (self.read_bytes(gpa_id, enc, sysmap1) === self.read_bytes(gpa_id, enc, sysmap2))
                || self.read_bytes(gpa_id, enc, sysmap1).is_Error() || self.read_bytes(
                gpa_id,
                enc,
                sysmap2,
            ).is_Error(),
    {
        if self.read_bytes(gpa_id, enc, sysmap1).is_Ok() {
            self.lemma_read_enc_byte_ok(sysmap1, gpa_id, enc);
        }
        if self.read_bytes(gpa_id, enc, sysmap2).is_Ok() {
            self.lemma_read_enc_byte_ok(sysmap2, gpa_id, enc);
        }
    }

    pub proof fn lemma_read_enc_ok_valid_model_eq(&self, other: &Self, gpa_id: GPAMemID)
        requires
            rmp_inv_sw(&other.rmp, gpa_id.memid),
            gpa_id.range.is_valid(),
            other.inv(),
            self.model1_eq(other, gpa_id.memid) || self.model2_eq(other),
        ensures
            other.get_enc_bytes_ok(gpa_id).is_None() ==> self.get_enc_bytes_ok(gpa_id).is_None(),
    {
        let gpa = gpa_id.range;
        let memid = gpa_id.memid;
        assert(rmp_inv_sw(&self.rmp, gpa_id.memid)) by {
            rmp_lemma_model_eq_inv(&self.rmp, &other.rmp, gpa_id.memid);
        }
        if other.get_enc_bytes_ok(gpa_id).is_None() {
            assert(!rmp_has_gpn_memid(&other.spec_rmp(), gpa.to_page(), memid));
            assert(!rmp_has_gpn_memid(&self.spec_rmp(), gpa.to_page(), memid)) by {
                assert(self.spec_rmp().dom() === other.spec_rmp().dom());
                assert forall|spn: SPN|
                    self.spec_rmp()[spn].view().spec_validated()
                        && self.spec_rmp()[spn].view().spec_asid() === memid.to_asid()
                        && self.spec_rmp().dom().contains(
                        spn,
                    ) implies #[trigger] self.spec_rmp()[spn].view().spec_gpn()
                    !== gpa.to_page() by {
                    assert(other.spec_rmp()[spn] === self.spec_rmp()[spn]);
                    assert(other.spec_rmp()[spn].view().spec_gpn() !== gpa.to_page()) by {
                        assert(!rmp_has_gpn_memid(&other.spec_rmp(), gpa.to_page(), memid));
                    }
                }
            }
        }
    }

    pub proof fn lemma_write_sm_int_ok(&self, memid: MemID, memop: MemOp<GuestPhy>, sysmap: SysMap)
        requires
            self.inv_sw(memid),
            self.inv(),
            self.inv_memid_int(memid),
            memtype(memid, memop.to_addr_memid().range.to_page()).is_sm_int(),
            self.op(sysmap, memop).is_Ok(),
            memop.is_valid(),
            memop.is_Write(),
            memid.is_vmpl0(),
        ensures
            memop.to_memid().is_sm(memid) || memop.to_memid().to_asid() !== memid.to_asid()
                || !memop.get_Write_1(),
    {
        reveal(RmpEntry::check_access);
        reveal(VRamDB::op);
        let rmp = self.spec_rmp();
        if memop.get_Write_1() {
            let gpn = memop.to_page();
            let op_memid = memop.to_memid();
            let spn = sysmap.translate(gpn);
            assert(spn.is_Some());
            let spn = spn.get_Some_0();
            assert(rmp[spn].view().check_vmpl(op_memid.to_vmpl(), Perm::Write));
            assert(rmp[spn].view().spec_gpn() === gpn);
            assert(rmp[spn].view().spec_asid() === op_memid.to_asid());
            assert(rmp[spn].inv()) by {
                reveal(rmp_inv);
            }
            if memop.to_memid().to_asid() === memid.to_asid() {
                assert(rmp_reverse(&rmp, memid, gpn) === spn);
                assert(memop.to_memid().is_sm(memid));
            }
        }
    }

    pub proof fn lemma_write_enc_must_has_gpn_in_rmp(
        &self,
        memid: MemID,
        memop: MemOp<GuestPhy>,
        sysmap: SysMap,
    )
        requires
            rmp_inv_sw(&self.rmp, memid),
            self.inv(),
            self.op(sysmap, memop).is_Ok(),
            memop.is_valid(),
            memop.is_Write(),
            memop.get_Write_1(),
        ensures
            self.get_enc_bytes_ok(memop.to_addr_memid()).is_Some(),
    {
        reveal(RmpEntry::check_access);
        reveal(VRamDB::op);
    }

    pub proof fn lemma_read_enc_ok_model1_eq(&self, other: &Self, gpa_id: GPAMemID)
        requires
            rmp_inv_sw(&other.rmp, gpa_id.memid),
            other.inv(),
            gpa_id.range.is_valid(),
            rmp_inv_memid_int(&other.rmp, gpa_id.memid),
            memtype(gpa_id.memid, gpa_id.range.to_page()).is_sm_int(),
            self.model1_eq(other, gpa_id.memid),
        ensures
            self.get_enc_bytes_ok(gpa_id).is_Some() ==> self.get_enc_bytes_ok(gpa_id)
                === other.get_enc_bytes_ok(gpa_id),
            other.get_enc_bytes_ok(gpa_id).is_None() ==> self.get_enc_bytes_ok(gpa_id).is_None(),
    {
        reveal(RmpEntry::check_access);
        self.lemma_read_enc_ok_valid_model_eq(other, gpa_id);
        let gpa = gpa_id.range;
        let memid = gpa_id.memid;
        let vmpl = memid.to_vmpl();
        assert(rmp_inv_sw(&self.rmp, gpa_id.memid)) by {
            rmp_lemma_model_eq_inv(&self.rmp, &other.rmp, memid);
        }
        assert(rmp_inv_memid_int(&self.rmp, memid)) by {
            rmp_lemma_model_eq_inv(&self.rmp, &other.rmp, memid);
        }
        let spn1 = rmp_reverse(&self.rmp, memid, gpa.to_page());
        let spn2 = rmp_reverse(&other.rmp, memid, gpa.to_page());
        let spmem1 = rmp_reverse_mem(&self.rmp, memid, gpa);
        let spmem2 = rmp_reverse_mem(&other.rmp, memid, gpa);
        let read_bytes1 = self.get_enc_bytes_ok(gpa_id);
        let read_bytes2 = other.get_enc_bytes_ok(gpa_id);
        if self.get_enc_bytes_ok(gpa_id).is_Some() {
            assert(self.rmp[spn1].view().spec_validated());
            assert(other.rmp[spn2].view().spec_validated());
            assert(self.rmp[spn1].view() === other.rmp[spn1].view());
            assert(other.rmp[spn1].view().spec_gpn() === gpa.to_page());
            assert(rmp_reverse(&other.rmp, memid, gpa.to_page()) === spn1);
            assert(spn1 === spn2 && spmem1 === spmem2);
            assert(read_bytes1 === read_bytes2) by {
                let bytes1 = self.spec_sram().read_bytes_by_asid(memid.to_asid(), spmem1);
                let bytes2 = other.spec_sram().read_bytes_by_asid(memid.to_asid(), spmem2);
                assert(bytes1 === bytes2) by {
                    assert forall|i: int| 0 <= i < spmem1.len() implies bytes1[i] === bytes2[i] by {
                        let spa = spmem1[i];
                        assert(spa.to_page() =~= spn1);
                        let rmpentry1 = self.rmp[spa.to_page()].view();
                        let rmpentry2 = other.rmp[spa.to_page()].view();
                        assert(rmpentry1.spec_validated() && rmpentry2.spec_validated());
                        assert(rmpentry1 === rmpentry2);
                        //assert(vmpl >= VMPL::VMPL0 ||  !other.rmp[spa.to_page()].view().check_vmpl(VMPL::VMPL0, Perm::Write));
                        assert(vmpl >= VMPL::VMPL1 || !other.rmp[spa.to_page()].view().check_vmpl(
                            VMPL::VMPL1,
                            Perm::Write,
                        )) by {
                            rmp_inv_memid_int(&other.rmp, gpa_id.memid);
                        }
                        assert(vmpl >= VMPL::VMPL2 || !other.rmp[spa.to_page()].view().check_vmpl(
                            VMPL::VMPL2,
                            Perm::Write,
                        ));
                        assert(vmpl >= VMPL::VMPL3 || !other.rmp[spa.to_page()].view().check_vmpl(
                            VMPL::VMPL3,
                            Perm::Write,
                        ));
                        assert(self.spec_sram().spec_data()[spa.value()]
                            === other.spec_sram().spec_data()[spa.value()]) by {
                            assert(self.model1_eq(other, memid));
                        }
                        assert(bytes1[i] === bytes2[i]);
                    }
                    assert(bytes1 =~~= (bytes2));
                }
            }
        }
    }

    pub proof fn lemma_read_enc_ok_model2_eq(&self, other: &Self, gpa_id: GPAMemID)
        requires
            rmp_inv_sw(&other.rmp, gpa_id.memid),
            other.inv(),
            gpa_id.range.is_valid(),
            self.model2_eq(other),
        ensures
            self.get_enc_bytes_ok(gpa_id).is_Some() ==> self.get_enc_bytes_ok(gpa_id)
                === other.get_enc_bytes_ok(gpa_id),
            other.get_enc_bytes_ok(gpa_id).is_None() ==> self.get_enc_bytes_ok(gpa_id).is_None(),
    {
        reveal(RmpEntry::check_access);
        self.lemma_read_enc_ok_valid_model_eq(other, gpa_id);
        let gpa = gpa_id.range;
        let memid = gpa_id.memid;
        assert(rmp_inv_sw(&self.rmp, gpa_id.memid)) by {
            rmp_lemma_model_eq_inv(&self.rmp, &other.rmp, memid);
        }
        let spn1 = rmp_reverse(&self.rmp, memid, gpa.to_page());
        let spn2 = rmp_reverse(&other.rmp, memid, gpa.to_page());
        let spmem1 = rmp_reverse_mem(&self.rmp, memid, gpa);
        let spmem2 = rmp_reverse_mem(&other.rmp, memid, gpa);
        let read_bytes1 = self.get_enc_bytes_ok(gpa_id);
        let read_bytes2 = other.get_enc_bytes_ok(gpa_id);
        if self.get_enc_bytes_ok(gpa_id).is_Some() {
            assert(self.rmp[spn1].view().spec_validated());
            assert(other.rmp[spn2].view().spec_validated());
            assert(self.rmp[spn1].view() === other.rmp[spn1].view());
            assert(other.rmp[spn1].view().spec_gpn() === gpa.to_page());
            assert(rmp_reverse(&other.rmp, memid, gpa.to_page()) === spn1);
            assert(spn1 === spn2 && spmem1 === spmem2);
            assert(read_bytes1 === read_bytes2) by {
                let bytes1 = self.spec_sram().read_bytes_by_asid(memid.to_asid(), spmem1);
                let bytes2 = other.spec_sram().read_bytes_by_asid(memid.to_asid(), spmem2);
                assert(bytes1 === bytes2) by {
                    assert forall|i: int| 0 <= i < spmem1.len() implies bytes1[i] === bytes2[i] by {
                        let spa = spmem1[i];
                        assert(spa.to_page() =~= spn1);
                        let rmpentry1 = self.rmp[spa.to_page()].view();
                        let rmpentry2 = other.rmp[spa.to_page()].view();
                        assert(rmpentry1.spec_validated() && rmpentry2.spec_validated());
                        assert(rmpentry1 === rmpentry2);
                        assert(self.spec_sram().spec_data()[spa.value()]
                            === other.spec_sram().spec_data()[spa.value()]) by {
                            assert(self.model2_eq(other));
                        }
                        assert(bytes1[i] === bytes2[i]);
                    }
                    assert(bytes1 =~~= (bytes2));
                }
            }
        }
    }

    pub proof fn lemma_model_eq_inv(self, other: &Self, memid: MemID)
        requires
            self.model1_eq(other, memid),
            other.inv(),
        ensures
            self.inv(),
            other.inv_sw(memid) ==> self.inv_sw(memid),
            other.inv_memid_int(memid) ==> self.inv_memid_int(memid),
    {
        reveal(VRamDB::inv);
        rmp_lemma_model_eq_inv(&self.spec_rmp(), &other.spec_rmp(), memid);
        assert(self.spec_sram().inv());
    }

    pub proof fn lemma_possible_ops_mod_enc_bytes(
        self,
        anysysmap: SysMap,
        op: MemOp<GuestPhy>,
        gpa: GPA,
        memid: MemID,
    )
        requires
            gpa.is_valid(),
            self.get_enc_byte_ok(memid, gpa) !== self.op(anysysmap, op).to_result().get_enc_byte_ok(
                memid,
                gpa,
            ),
            memid.to_vmpl().is_VMPL0(),
            op.to_memid().is_sm(memid),
        ensures
            op.is_Write() || (op.is_RmpOp()),
    {
        reveal(VRamDB::op);
    }
}

} // verus!
