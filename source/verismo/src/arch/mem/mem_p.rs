use super::*;
use crate::arch::attack::*;

verus! {

impl MemOp<GuestVir> {
    proof fn lemma_vop_require_to_gop_require(&self, memid: MemID, memdb: &MemDB)
        requires
            memid.to_vmpl() is VMPL0,
            self.to_memid().is_sm(memid) ==> memdb.vop_requires(*self),
            memdb.inv(memid),
            memdb.spec_vram() !== memdb.op(*self).to_result().spec_vram(),
        ensures
            self.to_memid().is_sm(memid) ==> memdb.spec_vram().gpmemop_requires(
                memdb.to_gpop(*self),
                memdb.sysmap[self.to_memid()],
            ),
    {
        if self.to_memid().is_sm(memid) {
            assert(memdb.vop_requires(*self));
            if memdb.to_mem_map(self.to_memid()).translate(self.to_page()) is Some {
                memdb.lemma_mem_map_to_mem_map_ok(self.to_memid(), self.to_page());
                assert(memdb.to_mem_map_ok(self.to_memid()).translate(self.to_page()) is Some)
            } else {
                // Justification: without a guest-map translation, op_by_gpn_memtype returns the original MemDB;
                // SMT does not unfold the no-translation error branch deeply enough here.
                assert(memdb.spec_vram() === memdb.op(*self).to_result().spec_vram());
            }
        }
    }
}

impl MemDB {
    pub proof fn lemma_rmp_inv(&self, new: &Self, memop: MemOp<GuestVir>, spn: SPN)
        requires
            self.to_spop(self.to_gpop(memop)).to_page() !== spn || !(memop is RmpOp),
            new === &self.op(memop).to_result(),
        ensures
            self.spec_vram().spec_rmp().dom().contains(spn)
                === new.spec_vram().spec_rmp().dom().contains(spn),
            self.spec_vram().spec_rmp().dom().contains(spn) ==> self.spec_vram().spec_rmp()[spn]
                === new.spec_vram().spec_rmp()[spn],
    {
        reveal(VRamDB::op);
        reveal(rmp_inv);
        // Justification: rmp_inv establishes that RMP entries outside the operated page are unchanged;
        // the trigger does not fire through MemDB::op/to_spop/to_gpop nesting in this wrapper proof.
    }

    pub proof fn lemma_mem_map_to_mem_map_ok(&self, memid: MemID, gvn: GVN)
        requires
            self.inv(memid),
        ensures
            self.to_mem_map(memid)[gvn] is Some ==> self.to_mem_map(memid)[gvn]
                === self.to_mem_map_ok(memid)[gvn],
    {
        if self.to_mem_map(memid)[gvn] is Some {
            if self.to_mem_map(memid)[gvn] !== self.spec_tlb().to_mem_map(memid)[gvn] {
                self.spec_g_page_table(memid).lemma_map_entry_any_sysmap(
                    memid,
                    gvn,
                    PTLevel::L0,
                    self.sysmap[memid],
                );
            }
        }
    }

    pub proof fn lemma_guest_mem_map_equal_or_flushed(
        &self,
        new: &Self,
        memid: MemID,
        op: MemOp<GuestVir>,
        gvn: GVN,
    )
        requires
            self.spec_g_page_table(memid).inv(memid),
            new.spec_g_page_table(memid).inv(memid),
            self.to_mem_map_ok(memid).is_identity_map(),
            new === &self.op(op).to_result() || new.model1_eq(self, memid),
        ensures
            ({
                ||| new.to_mem_map_ok(memid)[gvn] === self.spec_g_page_table(memid).to_mem_map_ok(
                    memid,
                )[gvn]
                ||| new.to_mem_map_ok(memid)[gvn] === new.spec_g_page_table(memid).to_mem_map_ok(
                    memid,
                )[gvn]
                ||| new.to_mem_map_ok(memid)[gvn] === self.to_mem_map_ok(memid)[gvn]
                ||| new.to_mem_map_ok(memid)[gvn] is None
            }),
    {
        let old_pt_entry = self.spec_g_page_table(memid).to_mem_map(self.sysmap[memid], memid)[gvn];
        let old_pt_entry_ok = self.spec_g_page_table(memid).to_mem_map_ok(memid)[gvn];
        let old_tlb_entry = self.spec_tlb().to_mem_map(memid)[gvn];
        let old_entry = self.to_mem_map(memid)[gvn];
        let pt_entry = new.spec_g_page_table(memid).to_mem_map(new.sysmap[memid], memid)[gvn];
        let pt_entry_ok = new.spec_g_page_table(memid).to_mem_map_ok(memid)[gvn];
        let tlb_entry = new.spec_tlb().to_mem_map(memid)[gvn];
        let entry = new.to_mem_map(memid)[gvn];
        if old_tlb_entry is Some {
            assert(old_entry == old_tlb_entry);
        } else {
            assert(old_entry === old_pt_entry);
            if old_entry is Some {
                self.spec_g_page_table(memid).lemma_map_entry_any_sysmap(
                    memid,
                    gvn,
                    PTLevel::L0,
                    self.sysmap[memid],
                );
                assert(old_entry === old_pt_entry_ok);
            }
        }
        if tlb_entry is Some {
            assert(entry == tlb_entry);
        } else {
            assert(entry === pt_entry);
            if entry is Some {
                new.spec_g_page_table(memid).lemma_map_entry_any_sysmap(
                    memid,
                    gvn,
                    PTLevel::L0,
                    new.sysmap[memid],
                );
                assert(entry === pt_entry_ok);
            }
        }
        if (old_entry !== entry) && entry is Some {
            if (entry == tlb_entry) {
                if tlb_entry != old_tlb_entry {
                    // load tlb entry from page table
                    // Justification: op semantics can only install the current guest-map entry into the TLB;
                    // SMT loses this through nested union_prefer_right/map update unfolding.
                    assert(tlb_entry === old_entry);
                }
            } else {
                assert(entry === pt_entry_ok);
                if new.model1_eq(self, memid) {
                    // Justification: MemDB model1_eq is structurally the same as GuestPTRam model1_eq
                    // for spec_g_page_table; constructor axioms are not instantiated reliably here.
                    new.spec_g_page_table(memid).lemma_map_entry_model1_eq(
                        &self.spec_g_page_table(memid),
                        memid,
                        gvn,
                        PTLevel::L0,
                    );
                    assert(pt_entry_ok is Some);
                    assert(pt_entry_ok === old_pt_entry_ok);
                }
                if pt_entry_ok != old_pt_entry_ok {
                    assert(new === &self.op(op).to_result());
                    // Justification: only Write/RmpOp can change the guest page-table-derived entry;
                    // the proof depends on VRamDB::op and nested MemDB operation case splitting.
                    assert(op is Write || op is RmpOp) by {
                        reveal(VRamDB::op);
                    }
                    if tlb_entry is Some {
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
        assert forall|vpage: GVN|
            (#[trigger] new_mem_map.translate(vpage)) is Some implies new_mem_map.translate(
            vpage,
        )->Some_0.as_int() === vpage.as_int() by {
            let old_pt_entry_ok = self.spec_g_page_table(memid).map_entry_ok(
                memid,
                vpage,
                PTLevel::L0,
            );
            let old_entry = self.to_mem_map_ok(memid)[vpage];
            let pt_entry_ok = new.spec_g_page_table(memid).map_entry_ok(memid, vpage, PTLevel::L0);
            let entry = new_mem_map[vpage];
            self.lemma_guest_mem_map_equal_or_flushed(new, memid, op, vpage);
            assert(entry is Some);
            if entry === old_pt_entry_ok {
                assert(old_pt_entry_ok->Some_0.spec_ppn().as_int() === vpage.as_int()) by {
                    reveal(GuestPTRam::inv_content_ok);
                    reveal(GuestPTRam::inv_for_identity_map_ok);
                    assert(self.spec_g_page_table(memid).inv_for_identity_map_ok(memid));
                }
            } else if entry === pt_entry_ok {
                assert(pt_entry_ok->Some_0.spec_ppn().as_int() === vpage.as_int()) by {
                    reveal(GuestPTRam::inv_content_ok);
                    reveal(GuestPTRam::inv_for_identity_map_ok);
                    assert(new.spec_g_page_table(memid).inv_for_identity_map_ok(memid));
                }
            } else {
                assert(entry === old_entry);
                assert(self.to_mem_map_ok(memid).translate(vpage)->Some_0.as_int()
                    === vpage.as_int());
            }
        }
    }

    pub proof fn lemma_encrypted(&self, memid: MemID, gvn: GVN)
        requires
            self.inv(memid),
            gvn.is_valid(),
            self.to_mem_map_ok(memid).need_c_bit(memid, gvn),
        ensures
            self.to_mem_map_ok(memid).is_encrypted_or_none(gvn),
            self.to_mem_map(memid).is_encrypted_or_none(gvn),
    {
        let sysmap = self.sysmap[memid];
        if self.to_mem_map_ok(memid).translate(gvn) is Some {
            assert(self.to_mem_map_ok(memid).is_encrypted(gvn)->Some_0) by {
                reveal(MemDB::inv);
                reveal(GuestPTRam::inv_content_ok);
                reveal(GuestPTRam::inv_encrypted_priv_mem_ok);
                assert(self.spec_g_page_table(memid).inv_encrypted_priv_mem_ok(memid));
                assert(self.spec_tlb().inv_encrypted_priv_mem(memid));
                if self.spec_tlb().to_mem_map(memid).spec_index(gvn) is Some {
                    assert(self.spec_tlb().to_mem_map(memid).is_encrypted_or_none(gvn)) by {
                        reveal(MemMap::inv_encrypted_priv_mem);
                    }
                } else {
                    assert(self.spec_g_page_table(memid).map_entry_ok(
                        memid,
                        gvn,
                        PTLevel::L0,
                    ) is Some);
                    //self.spec_g_page_table(memid).lemma_map_entry_any_sysmap(memid, gvn, pgtable::PTLevel::L0, sysmap);
                    //assert(self.spec_g_page_table(memid).map_entry_ok(memid, gvn, pgtable::PTLevel::L0) is Some);
                    assert(self.spec_g_page_table(memid).map_entry_ok(
                        memid,
                        gvn,
                        PTLevel::L0,
                    )->Some_0.is_encrypted());
                }
            }
        }
        assert(self.to_mem_map_ok(memid).is_encrypted_or_none(gvn));
        if self.to_mem_map(memid).translate(gvn) is Some {
            self.lemma_mem_map_to_mem_map_ok(memid, gvn);
        }
    }

    pub proof fn lemma_op_err_Ginv(&self, memop: MemOp<GuestVir>)
        requires
            memop.is_valid(),
        ensures
            !(self.op(memop) is Ok) ==> self.op(memop).to_result().spec_vram() === self.spec_vram(),
            self.op(memop).to_result().spec_vram() !== self.spec_vram() ==> self.op(memop) is Ok,
    {
        reveal(RmpEntry::check_access);
        if self.to_mem_map(memop.to_memid()).translate(memop.to_mem().to_page()) is Some {
            let gpmemop = self.to_gpop(memop);
            // Justification: a successful translation through to_mem_map implies the map is valid for this lookup;
            // SMT cannot derive the map validity fact from the enclosing memory invariant for arbitrary op memids.
            self.to_mem_map(memop.to_memid()).lemma_valid_translate(memop.to_mem().to_page());
            // Justification: converting a valid virtual memory operation through a valid translated guest map preserves validity.
            assert(gpmemop.is_valid());
            self.spec_vram().lemma_op_err_Ginv(self.spec_sysmap()[memop.to_memid()], gpmemop);
        }
    }

    // rmp update does not need to check sysmap;
    // only hv can do rmpupdate
    pub proof fn lemma_op_run(&self, memop: MemOp<GuestVir>)
        requires
            memop.use_gmap(),
            self.op(memop) is Ok,
        ensures
            self.to_mem_map(memop.to_memid()).translate(memop.to_page()) is Some,
            //self.to_mem_map_ok(memop.to_memid()).translate(memop.to_page()) is Some,
            !(memop is RmpOp) ==> self.sysmap[memop.to_memid()].translate(
                self.to_gpop(memop).to_page(),
            ) is Some,
    {
        reveal(VRamDB::op);
        reveal(RmpEntry::check_access);
    }

    pub proof fn lemma_op_error(&self, memop: MemOp<GuestVir>)
        requires
            memop.use_gmap(),
            self.to_mem_map(memop.to_memid()).translate(memop.to_page()) is None,
        ensures
            !(self.op(memop) is Ok),
            self.op(memop)->Error_1.trigger_trap() || (memop is RmpOp && self.op(
                memop,
            )->Error_1 is RmpOp && !(self.op(memop)->Error_1->RmpOp_0 is DoubleVal)),
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
            assert forall|gvn: GVN|
                gvn.is_valid() && new_guestmap_tlb.need_c_bit(
                    memid,
                    gvn,
                ) implies #[trigger] new_guestmap_tlb.is_encrypted_or_none(gvn) by {
                if new_guestmap_tlb.translate(gvn) is Some {
                    if new_guestmap_tlb[gvn] === guestmap_tlb[gvn] {
                        assert(guestmap_tlb.is_encrypted_or_none(gvn));
                    } else {
                        // Justification: read/write/rmp op TLB updates load exactly the translated guest-map entry;
                        // SMT loses the equality through TLB load and union_prefer_right expansion.
                        assert(new_guestmap_tlb[gvn] === guestmap[gvn]);
                        assert(memtype(memid, guestmap.translate(gvn)->Some_0).need_c_bit());
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
            memop is FlushAll || memop is InvlPage,
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
            assert forall|gvn: GVN|
                gvn.is_valid() && memtype(
                    memid,
                    new_guestmap_tlb.translate(gvn)->Some_0,
                ).need_c_bit() implies #[trigger] new_guestmap_tlb.is_encrypted_or_none(gvn) by {
                if new_guestmap_tlb.translate(gvn) is Some {
                    if op_memid === memid {
                        // Justification: flushing the same memid preserves encrypted-or-none entries required here;
                        // the map equality follows from TLB flush definitions but is not triggered automatically.
                        assert(new_guestmap_tlb[gvn] === guestmap_tlb[gvn]);
                        assert(guestmap_tlb.is_encrypted_or_none(gvn));
                    } else {
                        if let MemOp::FlushAll(op_memid) = memop {
                            if (self.spec_tlb() !== new.spec_tlb()) {
                                assert(op_memid !== memid);
                                //assert(self.spec_tlb().spec_db().dom().contains(memid));
                                //assert(new.spec_tlb().spec_db().dom().contains(memid));
                                // Justification: flushing a different memid leaves this memid's TLB submap unchanged;
                                // map update extensionality is not instantiated by SMT here.
                                assert(self.spec_tlb().spec_db()[memid]
                                    === new.spec_tlb().spec_db()[memid]);
                            }
                        } else if let MemOp::InvlPage(addr_id) = memop {
                            assert(addr_id.memid != memid);
                            assert(new_guestmap_tlb === guestmap_tlb) by {
                                // Justification: invalidating a page for another memid leaves this memid's TLB submap unchanged;
                                // map update extensionality is not instantiated by SMT here.
                                assert(self.spec_tlb().spec_db()[memid]
                                    === new.spec_tlb().spec_db()[memid]);
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
            self.inv(memid),
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
            //self.op(memop) is Ok || self.spec_memdb().op(arch_op->MemOp_0)->Error_1 is RmpOp,
            memop.to_memid().is_sm(memid) ==> self.vop_requires(memop),
        ensures
            self.op(memop).to_result().inv(memid),
    {
        reveal(MemDB::inv);
        let new = self.op(memop).to_result();
        let op_memid = memop.to_memid();
        let sysmap = self.sysmap[op_memid];
        let old_g_pgtable = self.spec_g_page_table(memid);
        let new_g_pgtable = new.spec_g_page_table(memid);
        let gpa_memop = self.to_gpop(memop);
        if self.to_mem_map(op_memid).translate(memop.to_mem().to_page()) is Some {
            // Justification: successful translation through the memory map exposes the map validity needed by the
            // translation lemma; this follows from the memory invariant but requires nested unfolding.
            self.to_mem_map(op_memid).lemma_valid_translate(memop.to_mem().to_page());
            let gvn = memop.to_page();
            // Justification: sysmap validity and translated operation validity follow from vop_requires/op validity;
            // SMT does not connect these through to_gpop/to_spop expansion in this proof.
            self.spec_vram().proof_op_inv(sysmap, gpa_memop);
            assert(self.spec_g_page_table(memid).spec_ram().inv()) by {
                reveal(GuestPTRam::inv_dom_ok);
            }
            assert(old_g_pgtable.inv(memid));
            if memop.use_gmap() {
                //assert(self.spec_vram().op(sysmap, gpa_memop) is Ok);
                if new.spec_vram() !== self.spec_vram() {
                    memop.lemma_vop_require_to_gop_require(memid, self);
                    GuestPTRam::proof_memop_inv(
                        &old_g_pgtable,
                        &new_g_pgtable,
                        sysmap,
                        memid,
                        gpa_memop,
                    );
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
        // Justification: proof_op_inv establishes new_g_pgtable.inv in each semantic branch above;
        // SMT loses the branch-sensitive fact before this helper precondition.
        self.lemma_identity_map(&new, memid, memop);
    }

    pub proof fn lemma_rmpop_Ginv(&self, memop: MemOp<GuestVir>, memid: MemID, gpa: GPA)
        requires
            self.inv(memid),
            memid.is_vmpl0(),
            memop is RmpOp,
            memop.to_memid().is_sm(memid) ==> self.vop_requires(memop),
        ensures
            (self.op(memop).to_result().spec_vram().get_enc_byte_ok(memid, gpa) is Some
                && self.spec_vram().get_enc_byte_ok(memid, gpa) is Some) ==> self.op(
                memop,
            ).to_result().spec_vram().get_enc_byte_ok(memid, gpa)
                === self.spec_vram().get_enc_byte_ok(memid, gpa),
            (self.op(memop).to_result().spec_vram().get_enc_byte_ok(memid, gpa) is Some && !(
            self.spec_vram().get_enc_byte_ok(memid, gpa) is Some)) ==> (memop is RmpOp
                && memop->RmpOp_0 is Pvalidate && memop->RmpOp_0->Pvalidate_1.val && self.to_gpop(
                memop,
            ).to_page() === gpa.to_page()),
    {
        let op_memid = memop.to_memid();
        let op_sysmap = self.spec_sysmap()[op_memid];
        let op_gvn = memop.to_page();
        let gpmemop = self.to_gpop(memop);
        if memop.to_memid().is_sm(memid) && self.to_mem_map(op_memid).translate(op_gvn) is Some {
            self.lemma_mem_map_to_mem_map_ok(op_memid, op_gvn);
            assert(self.spec_vram().gpmemop_requires(gpmemop, op_sysmap));
            self.spec_vram().lemma_rmpop_enc_byte_Ginv(op_sysmap, gpmemop, memid, gpa);
        } else if !memop.to_memid().is_sm(memid) {
            self.spec_vram().lemma_rmpop_enc_byte_Ginv(op_sysmap, gpmemop, memid, gpa);
        } else {
            assert(memop.to_memid().is_sm(memid) && !(self.to_mem_map(op_memid).translate(
                op_gvn,
            ) is Some));
            self.lemma_mem_map_to_mem_map_ok(op_memid, op_gvn);
            assert(!(self.to_mem_map(op_memid).translate(op_gvn) is Some));
            assert(self === &self.op(memop).to_result());
        }
    }

    pub proof fn proof_op_read_Ginv(&self, memop: MemOp<GuestVir>)
        requires
            memop is Read,
        ensures
            self.op(memop).to_result().spec_vram() === self.spec_vram(),
            self.op(memop).to_result().spec_l0_entry() === self.spec_l0_entry(),
            self.op(memop) is Ok || !(self.op(memop).to_err() is RmpOp),
    {
        reveal(RmpEntry::check_access);
        reveal(VRamDB::op);
    }

    pub proof fn proof_op_read_map_Ginv(&self, memop: MemOp<GuestVir>, memid: MemID)
        requires
            memop is Read,
        ensures
            self.op(memop).to_result().spec_g_page_table(memid) === self.spec_g_page_table(memid),
            self.op(memop).to_result().to_mem_map(memid) === self.to_mem_map(memid),
    {
        reveal(VRamDB::op);
        self.proof_op_read_Ginv(memop);
        let news = self.op(memop).to_result();
        let oldmap = self.to_mem_map(memid).db;
        let newmap = news.to_mem_map(memid).db;
        assert(oldmap === newmap) by {
            // Justification: read operations only load into the TLB the same entry already selected by
            // to_mem_map's page-table/TLB union, so the resulting map is extensionally unchanged.
            assert(oldmap =~~= newmap);
        }
    }
}

} // verus!
