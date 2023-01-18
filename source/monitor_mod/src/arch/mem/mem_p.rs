use super::*;
use crate::arch::attack::*;

verus! {
impl MemOp<GuestVir>
{
    proof fn lemma_vop_require_to_gop_require(&self, memid: MemID, memdb: &MemDB)
    requires
        memid.to_vmpl().is_VMPL0(),
        self.to_memid().is_sm(memid) ==> memdb.vop_requires(*self),
        memdb.inv(memid),
        memdb.spec_vram() !== memdb.op(*self).to_result().spec_vram(),
    ensures
        self.to_memid().is_sm(memid) ==> memdb.spec_vram().gpmemop_requires(memdb.to_gpop(*self), memdb.sysmap[self.to_memid()]),
    {
        if self.to_memid().is_sm(memid) {
            assert(memdb.vop_requires(*self));
            if memdb.to_mem_map(self.to_memid()).translate(self.to_page()).is_Some() {
                memdb.lemma_mem_map_to_mem_map_ok(self.to_memid(), self.to_page());
                assert(memdb.to_mem_map_ok(self.to_memid()).translate(self.to_page()).is_Some())
            } else {
                assert(memdb.spec_vram() === memdb.op(*self).to_result().spec_vram());
            }
        }
    }
}
impl MemDB
{
    pub proof fn lemma_rmp_inv(&self, new: &Self, memop: MemOp<GuestVir>, spn: SPN)
    requires
        self.to_spop(self.to_gpop(memop)).to_page() !== spn ||
        !memop.is_RmpOp(),
        new === &self.op(memop).to_result(),
    ensures
        self.spec_vram().spec_rmp().dom().contains(spn) === new.spec_vram().spec_rmp().dom().contains(spn),
        self.spec_vram().spec_rmp().dom().contains(spn) ==> self.spec_vram().spec_rmp()[spn] === new.spec_vram().spec_rmp()[spn]
    {
        reveal(VRamDB::op);
        reveal(rmp_inv);
    }

    pub proof fn lemma_mem_map_to_mem_map_ok(&self, memid: MemID, gvn: GVN)
    requires
        self.inv(memid),
    ensures
        self.to_mem_map(memid)[gvn].is_Some() ==> self.to_mem_map(memid)[gvn] === self.to_mem_map_ok(memid)[gvn]
    {
        if self.to_mem_map(memid)[gvn].is_Some() {
            if self.to_mem_map(memid)[gvn] !== self.spec_tlb().to_mem_map(memid)[gvn] {
                self.spec_g_page_table(memid).lemma_map_entry_any_sysmap(memid, gvn, PTLevel::L0, self.sysmap[memid]);
            }
        }
    }

    pub proof fn lemma_guest_mem_map_equal_or_flushed(&self, new: &Self, memid: MemID, op: MemOp<GuestVir>, gvn: GVN)
    requires
        self.spec_g_page_table(memid).inv(memid),
        new.spec_g_page_table(memid).inv(memid),
        self.to_mem_map_ok(memid).is_identity_map(),
        new === &self.op(op).to_result() || new.model1_eq(self, memid),
    ensures ({
        ||| new.to_mem_map_ok(memid)[gvn] === self.spec_g_page_table(memid).to_mem_map_ok(memid)[gvn]
        ||| new.to_mem_map_ok(memid)[gvn] === new.spec_g_page_table(memid).to_mem_map_ok(memid)[gvn]
        ||| new.to_mem_map_ok(memid)[gvn] === self.to_mem_map_ok(memid)[gvn]
        ||| new.to_mem_map_ok(memid)[gvn].is_None()
    })
    {
        let old_pt_entry = self.spec_g_page_table(memid).to_mem_map(self.sysmap[memid], memid)[gvn];
        let old_pt_entry_ok = self.spec_g_page_table(memid).to_mem_map_ok(memid)[gvn];
        let old_tlb_entry = self.spec_tlb().to_mem_map(memid)[gvn];
        let old_entry = self.to_mem_map(memid)[gvn];
        let pt_entry = new.spec_g_page_table(memid).to_mem_map(new.sysmap[memid], memid)[gvn];
        let pt_entry_ok = new.spec_g_page_table(memid).to_mem_map_ok(memid)[gvn];
        let tlb_entry = new.spec_tlb().to_mem_map(memid)[gvn];
        let entry = new.to_mem_map(memid)[gvn];

        if old_tlb_entry.is_Some() {
            assert(old_entry == old_tlb_entry);
        } else {
            assert(old_entry === old_pt_entry);
            if old_entry.is_Some() {
                self.spec_g_page_table(memid).lemma_map_entry_any_sysmap(memid, gvn, PTLevel::L0, self.sysmap[memid]);
                assert(old_entry === old_pt_entry_ok);
            }
        }
        if tlb_entry.is_Some() {
            assert(entry == tlb_entry);
        } else {
            assert(entry === pt_entry);
            if entry.is_Some() {
                new.spec_g_page_table(memid).lemma_map_entry_any_sysmap(memid, gvn, PTLevel::L0, new.sysmap[memid]);
                assert(entry === pt_entry_ok);
            }
        }
        if (old_entry !== entry) && entry.is_Some() {
            if (entry == tlb_entry) {
                if tlb_entry != old_tlb_entry {
                    // load tlb entry from page table
                    assert(tlb_entry === old_entry);
                }
            } else {
                assert(entry === pt_entry_ok);
                if new.model1_eq(self, memid) {
                    new.spec_g_page_table(memid).lemma_map_entry_model1_eq(&self.spec_g_page_table(memid), memid, gvn, PTLevel::L0);
                    assert(pt_entry_ok.is_Some());
                    assert(pt_entry_ok === old_pt_entry_ok);
                }
                if pt_entry_ok != old_pt_entry_ok {
                    assert(new === &self.op(op).to_result());
                    assert(op.is_Write() || op.is_RmpOp()) by {
                        reveal(VRamDB::op);
                    }
                    if tlb_entry.is_Some() {
                        if (tlb_entry !== old_tlb_entry) {
                            assert(tlb_entry === old_pt_entry_ok);
                        }
                    } else {
                        assert(entry == pt_entry_ok);
                    }
                }
            }
        }

    }

    pub proof fn lemma_identity_map(&self, new: &Self, memid: MemID, op: MemOp<GuestVir>)
    requires
        self.spec_g_page_table(memid).inv(memid),
        self.to_mem_map_ok(memid).is_identity_map(),
        new.spec_g_page_table(memid).inv(memid),
        new === &self.op(op).to_result() || new.model1_eq(self, memid),
    ensures
        new.to_mem_map_ok(memid).is_identity_map(),
    {
        reveal(MemMap::is_identity_map);
        let new_mem_map = new.to_mem_map_ok(memid);
        assert forall |vpage: GVN|
            (#[trigger]new_mem_map.translate(vpage)).is_Some()
        implies
            new_mem_map.translate(vpage).get_Some_0().as_int() === vpage.as_int()
        by {
            let old_pt_entry_ok = self.spec_g_page_table(memid).map_entry_ok(memid, vpage, PTLevel::L0);
            let old_entry = self.to_mem_map_ok(memid)[vpage];
            let pt_entry_ok = new.spec_g_page_table(memid).map_entry_ok(memid, vpage, PTLevel::L0);
            let entry = new_mem_map[vpage];
            self.lemma_guest_mem_map_equal_or_flushed(new, memid, op, vpage);
            assert(entry.is_Some());
            if entry === old_pt_entry_ok {
                assert(old_pt_entry_ok.get_Some_0().spec_ppn().as_int() === vpage.as_int()) by {
                    reveal(GuestPTRam::inv_content_ok);
                    reveal(GuestPTRam::inv_for_identity_map_ok);
                    assert(self.spec_g_page_table(memid).inv_for_identity_map_ok(memid));
                }
            } else if entry === pt_entry_ok {
                assert(pt_entry_ok.get_Some_0().spec_ppn().as_int() === vpage.as_int()) by {
                    reveal(GuestPTRam::inv_content_ok);
                    reveal(GuestPTRam::inv_for_identity_map_ok);
                    assert(new.spec_g_page_table(memid).inv_for_identity_map_ok(memid));
                }
            } else {
                assert(entry === old_entry);
                assert(self.to_mem_map_ok(memid).translate(vpage).get_Some_0().as_int() === vpage.as_int());
            }
        }
    }

    pub proof fn lemma_encrypted(&self, memid: MemID, gvn: GVN)
    requires
        self.inv(memid),
        gvn.is_valid(),
        self.to_mem_map_ok(memid).need_c_bit(memid, gvn)
    ensures
        self.to_mem_map_ok(memid).is_encrypted_or_none(gvn),
        self.to_mem_map(memid).is_encrypted_or_none(gvn),
    {
        let sysmap = self.sysmap[memid];
        if self.to_mem_map_ok(memid).translate(gvn).is_Some() {
            assert(self.to_mem_map_ok(memid).is_encrypted(gvn).get_Some_0()) by {
                reveal(MemDB::inv);
                reveal(GuestPTRam::inv_content_ok);
                reveal(GuestPTRam::inv_encrypted_priv_mem_ok);
                assert(self.spec_g_page_table(memid).inv_encrypted_priv_mem_ok(memid));
                assert(self.spec_tlb().inv_encrypted_priv_mem(memid));
                if self.spec_tlb().to_mem_map(memid).spec_index(gvn).is_Some() {
                    assert(self.spec_tlb().to_mem_map(memid).is_encrypted_or_none(gvn)) by {
                        reveal(MemMap::inv_encrypted_priv_mem);
                    }
                } else {
                    assert(self.spec_g_page_table(memid).map_entry_ok(memid, gvn, PTLevel::L0).is_Some());
                    //self.spec_g_page_table(memid).lemma_map_entry_any_sysmap(memid, gvn, pgtable::PTLevel::L0, sysmap);
                    //assert(self.spec_g_page_table(memid).map_entry_ok(memid, gvn, pgtable::PTLevel::L0).is_Some());
                    assert(self.spec_g_page_table(memid).map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0().is_encrypted());
                }
            }
        }
        assert(self.to_mem_map_ok(memid).is_encrypted_or_none(gvn));
        if self.to_mem_map(memid).translate(gvn).is_Some() {
            self.lemma_mem_map_to_mem_map_ok(memid, gvn);
        }
    }

    pub proof fn lemma_op_err_Ginv(&self, memop: MemOp<GuestVir>)
    requires
        memop.is_valid(),
    ensures
        !self.op(memop).is_Ok() ==> self.op(memop).to_result().spec_vram() === self.spec_vram(),
        self.op(memop).to_result().spec_vram() !== self.spec_vram() ==> self.op(memop).is_Ok(),
    {
        reveal(RmpEntry::check_access);
        if self.to_mem_map(memop.to_memid()).translate(memop.to_mem().to_page()).is_Some() {
        let gpmemop = self.to_gpop(memop);
        self.to_mem_map(memop.to_memid()).lemma_valid_translate(memop.to_mem().to_page());
        assert(gpmemop.is_valid());
        self.spec_vram().lemma_op_err_Ginv(self.spec_sysmap()[memop.to_memid()], gpmemop);
        }
    }

    // rmp update does not need to check sysmap;
    // only hv can do rmpupdate
    pub proof fn lemma_op_run(&self, memop: MemOp<GuestVir>)
    requires
        memop.use_gmap(),
        self.op(memop).is_Ok(),
    ensures
        self.to_mem_map(memop.to_memid()).translate(memop.to_page()).is_Some(),
        //self.to_mem_map_ok(memop.to_memid()).translate(memop.to_page()).is_Some(),
        !memop.is_RmpOp() ==> self.sysmap[memop.to_memid()].translate(self.to_gpop(memop).to_page()).is_Some(),
    {
        reveal(VRamDB::op);
        reveal(RmpEntry::check_access);
    }

    pub proof fn lemma_op_error(&self, memop: MemOp<GuestVir>)
    requires
        memop.use_gmap(),
        self.to_mem_map(memop.to_memid()).translate(memop.to_page()).is_None()
    ensures
        !self.op(memop).is_Ok(),
        self.op(memop).get_Error_1().trigger_trap() ||
        (memop.is_RmpOp() && self.op(memop).get_Error_1().is_RmpOp() && !self.op(memop).get_Error_1().get_RmpOp_0().is_DoubleVal())
    {
        reveal(VRamDB::op);
        reveal(RmpEntry::check_access);
    }

    //#[verifier(external_body)]
    proof fn lemma_op_read_or_write_tlb_inv(&self, new: &Self, memid: MemID, memop: MemOp<GuestVir>)
    requires
        self.inv(memid),
        memop.use_gmap(),
        new === &self.op(memop).to_result(),
    ensures
        new.spec_tlb().inv_encrypted_priv_mem(memid),
    {
        let guestmap = self.to_mem_map(memid);
        let new_guestmap = self.to_mem_map(memid);
        let guestmap_tlb = self.spec_tlb().to_mem_map(memid);
        let new_guestmap_tlb = new.spec_tlb().to_mem_map(memid);
        assert(new.spec_tlb().inv_encrypted_priv_mem(memid)) by {
            reveal(GuestPTRam::inv_content_ok);
            reveal(MemMap::inv_encrypted_priv_mem);
            assert forall |gvn: GVN| gvn.is_valid() &&
                new_guestmap_tlb.need_c_bit(memid, gvn)
            implies
                #[trigger] new_guestmap_tlb.is_encrypted_or_none(gvn)
            by {
                if new_guestmap_tlb.translate(gvn).is_Some() {
                    if new_guestmap_tlb[gvn] === guestmap_tlb[gvn] {
                        assert(guestmap_tlb.is_encrypted_or_none(gvn));
                    } else {
                        assert(new_guestmap_tlb[gvn] === guestmap[gvn]);
                        assert(memtype(memid, guestmap.translate(gvn).get_Some_0()).need_c_bit());
                        self.lemma_mem_map_to_mem_map_ok(memid, gvn);
                        self.lemma_encrypted(memid, gvn);
                    }
                }
            }
        }
    }

    proof fn lemma_op_flush_tlb_inv(&self, new: &Self, memid: MemID, memop: MemOp<GuestVir>)
    requires
        self.inv(memid),
        memop.is_FlushAll() || memop.is_InvlPage(),
        new === &self.op(memop).to_result(),
    ensures
        new.spec_tlb().inv_encrypted_priv_mem(memid),
    {
        let op_memid = memop.to_addr_memid().memid;
        let guestmap = self.to_mem_map(memid);
        let new_guestmap = self.to_mem_map(memid);
        let guestmap_tlb = self.spec_tlb().to_mem_map(memid);
        let new_guestmap_tlb = new.spec_tlb().to_mem_map(memid);
        assert(new.spec_tlb().inv_encrypted_priv_mem(memid)) by {
            reveal(GuestPTRam::inv_content_ok);
            reveal(MemMap::inv_encrypted_priv_mem);
            assert forall |gvn: GVN| gvn.is_valid() &&
                memtype(memid, new_guestmap_tlb.translate(gvn).get_Some_0()).need_c_bit()
            implies
                #[trigger] new_guestmap_tlb.is_encrypted_or_none(gvn)
            by {
                if new_guestmap_tlb.translate(gvn).is_Some() {
                    if op_memid === memid {
                        assert(new_guestmap_tlb[gvn] === guestmap_tlb[gvn]);
                        assert(guestmap_tlb.is_encrypted_or_none(gvn));
                    } else {
                        if let MemOp::FlushAll(op_memid) = memop {
                            if (self.spec_tlb() !== new.spec_tlb()) {
                                assert(op_memid !== memid);
                                //assert(self.spec_tlb().spec_db().dom().contains(memid));
                                //assert(new.spec_tlb().spec_db().dom().contains(memid));
                                assert(self.spec_tlb().spec_db()[memid] === new.spec_tlb().spec_db()[memid]);
                            }
                        } else if let MemOp::InvlPage(addr_id) = memop {
                            assert(addr_id.memid != memid);
                            assert(new_guestmap_tlb === guestmap_tlb) by {
                                assert(self.spec_tlb().spec_db()[memid] === new.spec_tlb().spec_db()[memid]);
                            }
                        }
                    }
                }
            }
        }
    }

    pub proof fn proof_model_eq1_inv(&self, oldmemdb: &Self, memid: MemID)
    requires
        oldmemdb.inv(memid),
        self.model1_eq(oldmemdb, memid),
    ensures
        self.inv(memid)
    {
        reveal(MemDB::inv);
        self.spec_vram().lemma_model_eq_inv(&oldmemdb.spec_vram(), memid);
        self.proof_model1_pgram_inv(oldmemdb, memid);
        self.spec_tlb().lemma_model1_inv_encrypted_priv_mem(&oldmemdb.spec_tlb(), memid);
        oldmemdb.lemma_identity_map(self, memid, spec_unused());
    }

    pub proof fn proof_op_inv(&self, memid: MemID, memop: MemOp<GuestVir>)
    requires
        self.inv(memid),
        memid.is_vmpl0(),
        memop.is_valid(),
        //self.op(memop).is_Ok() || self.spec_memdb().op(arch_op.get_MemOp_0()).get_Error_1().is_RmpOp(),
        memop.to_memid().is_sm(memid) ==> self.vop_requires(memop),
    ensures
        self.op(memop).to_result().inv(memid)
    {
        reveal(MemDB::inv);

        let new = self.op(memop).to_result();
        let op_memid = memop.to_memid();
        let sysmap = self.sysmap[op_memid];
        let old_g_pgtable = self.spec_g_page_table(memid);
        let new_g_pgtable = new.spec_g_page_table(memid);
        let gpa_memop = self.to_gpop(memop);
        if self.to_mem_map(op_memid).translate(memop.to_mem().to_page()).is_Some() {
            self.to_mem_map(op_memid).lemma_valid_translate(memop.to_mem().to_page());
            let gvn = memop.to_page();
            self.spec_vram().proof_op_inv(sysmap, gpa_memop);
            assert(self.spec_g_page_table(memid).spec_ram().inv()) by {
                reveal(GuestPTRam::inv_dom_ok);
            }
            assert(old_g_pgtable.inv(memid));
            if memop.use_gmap() {
                    //assert(self.spec_vram().op(sysmap, gpa_memop).is_Ok());
                if new.spec_vram() !== self.spec_vram() {
                    memop.lemma_vop_require_to_gop_require(memid, self);
                    GuestPTRam::proof_memop_inv(&old_g_pgtable, &new_g_pgtable, sysmap, memid, gpa_memop);
                    self.spec_vram().proof_op_inv_sw(sysmap, gpa_memop, memid);
                    assert(new_g_pgtable.inv(memid));
                    assert(new.spec_vram().inv());
                }
            } else {
                assert(new_g_pgtable === old_g_pgtable);
                assert(new.spec_vram() === self.spec_vram());
            }
        }
        match memop {
            MemOp::Read(_, _) => {
                self.lemma_op_read_or_write_tlb_inv(&new, memid, memop);
            },
            MemOp::Write(_, _, _) => {
                self.lemma_op_read_or_write_tlb_inv(&new, memid, memop);
            },
            MemOp::RmpOp(_) => {
                self.lemma_op_read_or_write_tlb_inv(&new, memid, memop);
            },
            MemOp::InvlPage(_) => {
                self.lemma_op_flush_tlb_inv(&new, memid, memop);
            },
            MemOp::FlushAll(_) => {
                self.lemma_op_flush_tlb_inv(&new, memid, memop);
            },
        }

        self.lemma_identity_map(&new, memid, memop);
    }

    pub proof fn lemma_rmpop_Ginv(&self, memop: MemOp<GuestVir>, memid: MemID, gpa: GPA)
    requires
        self.inv(memid),
        memid.is_vmpl0(),
        memop.is_RmpOp(),
        memop.to_memid().is_sm(memid) ==> self.vop_requires(memop),
    ensures
        (self.op(memop).to_result().spec_vram().get_enc_byte_ok(memid, gpa).is_Some() && self.spec_vram().get_enc_byte_ok(memid, gpa).is_Some()) ==>
            self.op(memop).to_result().spec_vram().get_enc_byte_ok(memid, gpa) === self.spec_vram().get_enc_byte_ok(memid, gpa),
        (self.op(memop).to_result().spec_vram().get_enc_byte_ok(memid, gpa).is_Some() && !self.spec_vram().get_enc_byte_ok(memid, gpa).is_Some()) ==>
            (memop.is_RmpOp() && memop.get_RmpOp_0().is_Pvalidate() && memop.get_RmpOp_0().get_Pvalidate_1().val &&
            self.to_gpop(memop).to_page() === gpa.to_page())
    {
        let op_memid = memop.to_memid();
        let op_sysmap = self.spec_sysmap()[op_memid];
        let op_gvn = memop.to_page();
        let gpmemop = self.to_gpop(memop);
        if memop.to_memid().is_sm(memid) && self.to_mem_map(op_memid).translate(op_gvn).is_Some() {
            self.lemma_mem_map_to_mem_map_ok(op_memid, op_gvn);
            assert(self.spec_vram().gpmemop_requires(gpmemop, op_sysmap));
            self.spec_vram().lemma_rmpop_enc_byte_Ginv(op_sysmap, gpmemop, memid, gpa);
        } else if !memop.to_memid().is_sm(memid) {
            self.spec_vram().lemma_rmpop_enc_byte_Ginv(op_sysmap, gpmemop, memid, gpa);
        } else {
            assert(memop.to_memid().is_sm(memid) && !self.to_mem_map(op_memid).translate(op_gvn).is_Some());
            self.lemma_mem_map_to_mem_map_ok(op_memid, op_gvn);
            assert(!self.to_mem_map(op_memid).translate(op_gvn).is_Some());
            assert(self === &self.op(memop).to_result());
        }
    }

    pub proof fn proof_op_read_Ginv(&self, memop: MemOp<GuestVir>)
    requires
        memop.is_Read(),
    ensures
        self.op(memop).to_result().spec_vram() === self.spec_vram(),
        self.op(memop).to_result().spec_l0_entry() === self.spec_l0_entry(),
        self.op(memop).is_Ok() || !self.op(memop).to_err().is_RmpOp(),
    {
        reveal(RmpEntry::check_access);
        reveal(VRamDB::op);
    }

    pub proof fn proof_op_read_map_Ginv(&self, memop: MemOp<GuestVir>, memid: MemID)
    requires
        memop.is_Read(),
    ensures
        self.op(memop).to_result().spec_g_page_table(memid) === self.spec_g_page_table(memid),
        self.op(memop).to_result().to_mem_map(memid) === self.to_mem_map(memid)
    {
        reveal(VRamDB::op);
        self.proof_op_read_Ginv(memop);
        let news =  self.op(memop).to_result();
        let oldmap = self.to_mem_map(memid).db;
        let newmap = news.to_mem_map(memid).db;
        assert(oldmap === newmap) by {
            assert forall|k|
                #[trigger] newmap.dom().contains(k)
            implies
                newmap[k] === oldmap[k]
            by {
            }
            assert(oldmap=~~=(newmap));
        }
    }
}
}
