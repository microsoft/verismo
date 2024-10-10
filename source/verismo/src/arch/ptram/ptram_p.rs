use super::*;
use crate::arch::attack::*;
use crate::arch::memop::MemOp;
use crate::arch::rmp::{RmpEntry, RmpMap, *};
use crate::arch::vram::VRamDB;

verus! {

impl GuestPTRam {
    /// Prove the correctness of our model
    /// Prove the PTRam contains all page table data,
    /// ensuring PTRam does not need to query DataRam.
    pub proof fn proof_pte_addr_must_in_ptram(
        &self,
        sysmap: SysMap,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
        map_gpa: GPMem,
    )
        requires
            self.inv(memid),
            map_gpa.is_valid(),
            gvn.is_valid(),
            self.spec_ram().inv_sw(memid),
            self.valid_access(memid, map_gpa, sysmap),
            self.map_entry_gpa(sysmap, memid, gvn, lvl).is_Some(),
            map_gpa === self.map_entry_gpa(sysmap, memid, gvn, lvl).get_Some_0(),
        ensures
            sysmap.translate(map_gpa.to_page()).is_Some(),
            self.spec_ram().rmp.dom().contains(sysmap.translate(map_gpa.to_page()).get_Some_0()),
    {
        reveal(GuestPTRam::inv_dom_ok);
        self.lemma_map_entry_gpa_any_sysmap(memid, gvn, lvl, sysmap);
        self.lemma_map_entry_gpa_is_pte_type(memid, gvn, lvl);
        assert(memtype(memid, map_gpa.to_page()).is_PTE());
    }

    /*pub proof fn proof_mem_map_le_mem_map_ok(&self, sysmap: SysMap, memid: MemID, gvn: GVN, pt_rmp: RmpMap)
    requires
        self.inv(memid),
    ensures
        self.to_mem_map(sysmap, memid).db.le(self.to_mem_map_ok(memid).db)
    {
        assert forall |gvn|
            self.to_mem_map(sysmap, memid).db[gvn].is_Some()
        implies
            #[trigger] self.to_mem_map(sysmap, memid)[gvn] === self.to_mem_map_ok(memid)[gvn]
        by {
            self.lemma_map_entry_any_sysmap(memid, gvn, PTLevel::L0, sysmap);
        }
    }*/
    /// Prove the correctness of our model
    /// Prove the guest mapping is the identity mapping;
    pub proof fn proof_identity_mapping(
        &self,
        sysmap: SysMap,
        memid: MemID,
        gvn: GVN,
        pt_rmp: RmpMap,
    )
        requires
            self.inv(memid),
            gvn.is_valid(),
        ensures
            self.to_mem_map(sysmap, memid).is_identity_map(),
    {
        let memmap = self.to_mem_map(sysmap, memid);
        assert forall|gvn: GVN|
            gvn.is_valid() && (#[trigger] memmap.translate(gvn)).is_Some() implies memmap.translate(
            gvn,
        ).get_Some_0().as_int() == gvn.as_int() by {
            assert(self.map_entry(sysmap, memid, gvn, PTLevel::L0).is_Some());
            let ppn = self.map_entry(sysmap, memid, gvn, PTLevel::L0).get_Some_0().spec_ppn();
            assert(ppn == memmap.translate(gvn).get_Some_0());
            reveal(GuestPTRam::inv_content_ok);
            reveal(GuestPTRam::inv_for_identity_map_ok);
            self.lemma_map_entry_any_sysmap(memid, gvn, PTLevel::L0, sysmap);
        }
        reveal(MemMap::<_, _>::is_identity_map);
    }

    #[verifier(external_body)]
    pub proof fn lemma_map_entry_gpa_valid(
        &self,
        sysmap: SysMap,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    )
        requires
            gvn.is_valid(),
            self.map_entry_gpa(sysmap, memid, gvn, lvl).is_Some(),
        ensures
            self.map_entry_gpa(sysmap, memid, gvn, lvl).get_Some_0().to_page().is_valid(),
    {
    }

    #[verifier(external_body)]
    pub proof fn lemma_map_entry_gpa_ok_valid(&self, memid: MemID, gvn: GVN, lvl: PTLevel)
        requires
            gvn.is_valid(),
            self.map_entry_gpa_ok(memid, gvn, lvl).is_Some(),
        ensures
            self.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0().to_page().is_valid(),
    {
    }

    pub proof fn lemma_map_entry_gpa_is_pte_type(&self, memid: MemID, gvn: GVN, lvl: PTLevel)
        requires
            self.inv(memid),
            gvn.is_valid(),
            self.map_entry_gpa_ok(memid, gvn, lvl).is_Some(),
        ensures
            memtype(memid, self.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0().to_page()).is_pt(
                lvl,
            ),
            self.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0().to_page().is_valid(),
    {
        self.lemma_map_entry_gpa_ok_valid(memid, gvn, lvl);
        let l0_entry = self.l0_entry(memid);
        let idx = lvl.spec_table_index(gvn.to_addr()) as nat;
        let pte_gpa_ok = self.map_entry_gpa_ok(memid, gvn, lvl);
        assert(0 <= idx < PT_ENTRY_NUM) by {
            lvl.proof_table_index_range(gvn.to_addr());
        }
        assert(memtype(memid, pte_gpa_ok.get_Some_0().to_page()).is_pt(lvl)) by {
            reveal(GuestPTRam::inv_content_ok);
            reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive_ok, 1);
            match lvl.parent_lvl() {
                Option::Some(next_lvl) => {
                    let prev_pte = self.map_entry_ok(memid, gvn, next_lvl);
                    assert(prev_pte.is_Some());
                    let prev_pte = prev_pte.get_Some_0();
                    prev_pte.lemma_each_table_is_one_page(idx);
                    assert(pte_gpa_ok.get_Some_0().to_page() === prev_pte.spec_ppn());
                    assert(self.inv_content_gpa_ok(memid, gvn));
                },
                Option::None => {
                    l0_entry.lemma_each_table_is_one_page(idx);
                    assert(pte_gpa_ok.get_Some_0().to_page() === l0_entry.spec_ppn());
                },
            }
        }
    }

    /// Prove inv when PTE update meets requirements
    pub proof fn proof_memop_inv(
        old_pt: &Self,
        new_pt: &Self,
        sysmap: SysMap,
        memid: MemID,
        memop: MemOp<GuestPhy>,
    )
        requires
            old_pt.inv(memid),
            memid.is_vmpl0(),
            memop.is_valid(),
            new_pt === &old_pt.spec_set_ram(old_pt.ram.op(sysmap, memop).to_result()),
            //old_pt.spec_ram().op(sysmap, memop).is_Ok(),
            memop.to_memid().is_sm(memid) ==> old_pt.spec_ram().gpmemop_requires(
                memop,
                sysmap,
            ),
    //memop.is_Write() ==> Self::write_pt_requires(&old_pt.spec_ram(), memop.to_addr_memid(), memop.get_Write_1(), memop.get_Write_2(), sysmap)

        ensures
            new_pt.inv(memid),
    {
        reveal(VRamDB::op);
        old_pt.spec_ram().proof_op_inv_sw(sysmap, memop, memid);
        assert(new_pt.spec_ram().inv_sw(memid));
        assert(new_pt.spec_ram().inv_memid_int(memid));
        match memop {
            MemOp::Read(gpmem_id, enc) => {
                if old_pt.ram.op(sysmap, memop).is_Ok() {
                    Self::lemma_safe_read(memid, old_pt, new_pt, gpmem_id, enc, sysmap);
                }
            },
            MemOp::Write(gpa_id, enc, data) => {
                if old_pt.ram.op(sysmap, memop).is_Ok() {
                    Self::lemma_safe_write(memid, old_pt, new_pt, gpa_id, enc, data, sysmap);
                    //assume(new_pt.inv(memid));
                }
            },
            MemOp::InvlPage(gpa_id) => {},
            MemOp::FlushAll(_) => {},
            MemOp::RmpOp(rmpop) => {
                assume(new_pt.inv(memid));
            },
        }
    }

    proof fn lemma_safe_read(
        memid: MemID,
        old_pt: &Self,
        new_pt: &Self,
        gpmem_id: GPAMemID,
        enc: bool,
        sysmap: SysMap,
    )
        requires
            old_pt.inv(memid),
            gpmem_id.range.is_valid(),
            new_pt === &old_pt.spec_set_ram(
                old_pt.spec_ram().op_read(gpmem_id, enc, sysmap).to_result(),
            ),
        ensures
            new_pt.inv_dom_ok(memid),
            new_pt.inv_content_ok(memid),
    {
        reveal(GuestPTRam::inv_dom_ok);
        reveal(VRamDB::op);
        let ram = old_pt.spec_ram();
        ram.proof_op_inv(sysmap, MemOp::Read(gpmem_id, enc));
    }

    proof fn lemma_write_pte_inv_ppn_enc(
        old_pt: &Self,
        new_pt: &Self,
        sysmap: SysMap,
        memid: MemID,
        memop: MemOp<GuestPhy>,
        gvn: GVN,
        lvl: PTLevel,
    )
        requires
            old_pt.inv(memid),
            memid.is_vmpl0(),
            //old_pt.spec_ram().inv_enc(memid),
            gvn.is_valid(),
            memop.is_valid(),
            memop.is_Write(),
            memop.to_memid().is_sm(memid) ==> old_pt.spec_ram().gpmemop_requires(memop, sysmap),
            //Self::write_pt_requires(&old_pt.spec_ram(), memop.to_addr_memid(), memop.get_Write_1(), memop.get_Write_2(), sysmap),
            //memid === memop.to_addr_memid().memid,
            new_pt.l0_entry(memid) === old_pt.l0_entry(memid),
            new_pt === &old_pt.spec_set_ram(old_pt.spec_ram().op(sysmap, memop).to_result()),
            new_pt.map_entry_ok(memid, gvn, lvl).is_Some(),
            old_pt.spec_ram().op(sysmap, memop).is_Ok(),
        ensures
            old_pt.map_entry_exe_ok(memid, gvn, lvl).is_Some(),
            (old_pt.need_c_bit(memid, gvn) && lvl.is_L0()) ==> new_pt.map_entry_ok(
                memid,
                gvn,
                lvl,
            ).get_Some_0().is_encrypted(),
            new_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn() === old_pt.map_entry_ok(
                memid,
                gvn,
                lvl,
            ).get_Some_0().spec_ppn(),
    {
        Self::lemma_write_pte_inv_ppn(old_pt, new_pt, sysmap, memid, memop, gvn, lvl);
        let wgpmem = memop.to_mem();
        let write_pte: GuestPTEntry = stream_to_data(memop.get_Write_2());
        let old_pte_gpa = old_pt.map_entry_gpa_ok(memid, gvn, lvl);
        let old_gpn = old_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn();
        assert(memtype(memid, old_pte_gpa.get_Some_0().to_page()).is_pt(lvl)) by {
            old_pt.lemma_map_entry_gpa_is_pte_type(memid, gvn, lvl);
        }
        let old_pte = old_pt.map_entry_exe_ok(memid, gvn, lvl);
        if old_pte_gpa.get_Some_0() === wgpmem && memop.to_memid().is_sm(memid)
            && memop.to_memid().to_asid() == memid.to_asid() {
            assert(old_pte.is_Some());
            assert(old_pte === old_pt.spec_ram().get_enc_data_ok::<GuestPTEntry>(
                AddrMemID { range: wgpmem, memid },
            ));
            assert(old_pt.spec_ram().op(sysmap, memop).is_Ok());
            assert(old_pte.is_Some());
            assert(write_pte.view().spec_ppn() === old_pte.get_Some_0().view().spec_ppn());
            if old_pt.need_c_bit(memid, gvn) && lvl.is_L0() {
                assert(write_pte.view().is_encrypted());
            }
        }
        if old_pt.need_c_bit(memid, gvn) && lvl.is_L0() {
            reveal(GuestPTRam::inv_content_ok);
            reveal(GuestPTRam::inv_encrypted_priv_mem_ok);
            assert(old_pt.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0()
                === old_pte.get_Some_0().view());
            assert(old_pte.get_Some_0().view().is_encrypted());
        }
    }

    /*proof fn lemma_write_pte_inv_ppn(old_pt: &Self, new_pt: &Self, sysmap: SysMap, memid: MemID, memop: MemOp<GuestPhy>, gvn: GVN, lvl: PTLevel)
    requires
        old_pt.inv(memid),
        memid.is_vmpl0(),
        gvn.is_valid(),
        memop.is_valid(),
        memop.is_Write(),
        memop.to_memid().is_sm(memid) ==> old_pt.spec_ram().gpmemop_requires(memop, sysmap),
        new_pt.l0_entry(memid) === old_pt.l0_entry(memid),
        new_pt === &old_pt.spec_set_ram(old_pt.spec_ram().op(sysmap, memop).to_result()),
        new_pt.map_entry_exe_ok(memid, gvn, lvl).is_Some(),
        old_pt.spec_ram().op(sysmap, memop).is_Ok(),
    ensures
        old_pt.map_entry_exe_ok(memid, gvn, lvl).is_Some(),
        ({
            ||| old_pt.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0() !== memop.to_mem()
            ||| !memop.to_memid().is_sm(memid)
            ||| memop.to_memid().to_asid() !== memid.to_asid()
        }) ==> {
            new_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0() === old_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0()
        },
        ({
            &&& old_pt.map_entry_gpa_ok(memid, gvn, lvl).get_Some_0() === memop.to_mem()
            &&& memop.to_memid().is_sm(memid)
            &&& memop.to_memid().to_asid() == memid.to_asid()
        }) ==> {
            new_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0() === stream_to_data(memop.get_Write_2()) &&
            new_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0().view().spec_ppn() === old_pt.map_entry_exe_ok(memid, gvn, lvl).get_Some_0().view().spec_ppn()
        }
    decreases
        lvl.as_int(),
    {
        let pte = new_pt.map_entry_exe_ok(memid, gvn, lvl);
        let old_pte = old_pt.map_entry_exe_ok(memid, gvn, lvl);

        let pte_gpa = new_pt.map_entry_gpa_ok(memid, gvn, lvl);
        let old_pte_gpa = old_pt.map_entry_gpa_ok(memid, gvn, lvl);

        match lvl.parent_lvl() {
            Option::Some(next_lvl) => {
                Self::lemma_write_pte_inv_ppn(old_pt, new_pt, sysmap, memid, memop, gvn, next_lvl);
                assert(pte_gpa === old_pte_gpa);
                assert(pte_gpa.is_Some());
            }
            _ => {
                assert(pte_gpa === old_pte_gpa) by {
                    reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive_ok, 1);
                }
            }
        }
        assert(pte_gpa === old_pte_gpa);
        assert(pte.is_Some());
        if let MemOp::Write(_, enc, data) = memop {
            let write_pte: GuestPTEntry = stream_to_data(data);
            let gpmem_id = memop.to_addr_memid();
            let AddrMemID {range: wgpmem, memid: op_memid} = gpmem_id;
            assert(old_pt.spec_ram().inv()) by {
                reveal(GuestPTRam::inv_dom_ok);
            }
            let pte_gpa = pte_gpa.get_Some_0();
            assert(old_pt.map_entry_gpa_ok(memid, gvn, lvl).is_Some());
            let old_pte_gpa = old_pte_gpa.get_Some_0();
            assert(memtype(memid, old_pte_gpa.to_page()).is_PTE()) by {
                old_pt.lemma_map_entry_gpa_is_pte_type(memid, gvn, lvl);
            }
            assert(old_pte_gpa.to_page().is_valid()) by {
                old_pt.lemma_map_entry_gpa_ok_valid(memid, gvn, lvl);
            }
            reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive_ok, 1);
            if gpmem_id.memtype().is_PTE() {
                old_pt.spec_ram().lemma_write_sm_int_ok(memid, memop, sysmap);
                if !memop.to_memid().is_sm(memid) || !enc {
                    old_pt.spec_ram().lemma_write_bytes_effect_by_other_vm_or_shared(&new_pt.spec_ram(), sysmap, memop, memid, old_pte_gpa);
                    assert(old_pt.spec_ram().get_enc_bytes_ok(AddrMemID{memid, range:old_pte_gpa}) ===
                        new_pt.spec_ram().get_enc_bytes_ok(AddrMemID{memid, range:old_pte_gpa}));
                    assert(pte === old_pte);
                } else {
                    assert(old_pt.spec_ram().gpmemop_requires(memop, sysmap));
                    assert(old_pt.spec_ram().pte_write_requires_nosysmap(gpmem_id, true, data));
                    if (old_pte.is_Some()) {
                        assert(rmp_has_gpn_memid(&old_pt.spec_ram().rmp, old_pte_gpa.to_page(), memid));
                        if(!rmp_has_gpn_memid(&old_pt.spec_ram().rmp, wgpmem.to_page(), op_memid)) {
                            assert(wgpmem.to_page() !== old_pte_gpa.to_page());
                        }
                    } else {
                        assert(!rmp_has_gpn_memid(&old_pt.spec_ram().rmp, old_pte_gpa.to_page(), memid));
                        old_pt.spec_ram().proof_rmp_check_access_rmp_has_gpn_memid(memop, sysmap);
                        assert(wgpmem.to_page() !== old_pte_gpa.to_page());
                        assert(wgpmem.disjoint(old_pte_gpa));
                    }
                    assert(spec_size::<GuestPTEntry>() == PT_ENTRY_SIZE);
                    assert(wgpmem.len() == 0 || (wgpmem.len() == PT_ENTRY_SIZE as int && wgpmem.is_aligned(PT_ENTRY_SIZE as int)) || wgpmem.disjoint(old_pte_gpa));
                    if (wgpmem.len() == PT_ENTRY_SIZE as int && wgpmem.is_aligned(PT_ENTRY_SIZE as int)) {
                        GPMem::lemma_aligned_mem_eq_or_disjoint(old_pte_gpa,
                            wgpmem, PT_ENTRY_SIZE as int);
                    }
                    if old_pte_gpa === wgpmem {
                        assert(enc) by {
                            reveal(RmpEntry::check_access);
                        }
                        old_pt.spec_ram().lemma_write_enc_bytes_effect_same_read(&new_pt.spec_ram(), sysmap, memop, memid, old_pte_gpa);
                        assert(op_memid.to_asid() === memid.to_asid());
                        assert(pte.get_Some_0() === write_pte);
                        assert(op_memid.is_sm(memid));
                        let old_value: Option<GuestPTEntry> = old_pt.spec_ram().get_enc_data_ok(memop.to_addr_memid());
                        assert(old_value.is_Some()) by {
                            old_pt.spec_ram().lemma_write_enc_must_has_gpn_in_rmp(memid, memop, sysmap);
                        }
                        assert(write_pte.view().spec_ppn() === old_pte.get_Some_0().view().spec_ppn());
                    } else {
                        old_pt.spec_ram().lemma_write_enc_bytes_effect_disjoint_read(&new_pt.spec_ram(), sysmap, memop, memid, old_pte_gpa);
                        assert(pte === old_pte);
                    }
                }
            } else {
                assert(memtype(memid, old_pte_gpa.to_page()).is_PTE());
                old_pte_gpa.lemma_disjoint(wgpmem);
                old_pt.spec_ram().lemma_write_enc_bytes_effect_disjoint_read(&new_pt.spec_ram(), sysmap, memop, memid, old_pte_gpa);
                assert(old_pt.spec_ram().get_enc_bytes_ok(AddrMemID{memid, range:old_pte_gpa}) ===
                        new_pt.spec_ram().get_enc_bytes_ok(AddrMemID{memid, range:old_pte_gpa}));
                assert(pte === old_pte);
            }
        }
    }*/
    //#[verifier(external_body)]
    proof fn lemma_safe_write(
        memid: MemID,
        old_pt: &Self,
        new_pt: &Self,
        gpa_id: AddrID<GuestPhy>,
        enc: bool,
        data: ByteStream,
        sysmap: SysMap,
    )
        requires
            old_pt.inv(memid),
            memid.is_vmpl0(),
            gpa_id.addr.is_valid(),
            old_pt.ram.op_write(gpa_id, enc, data, sysmap).is_Ok(),
            //sysmap.is_one_to_one_map(),
            new_pt === &old_pt.spec_set_ram(
                old_pt.spec_ram().op(sysmap, MemOp::Write(gpa_id, enc, data)).to_result(),
            ),
            //Self::write_pt_requires(&old_pt.spec_ram(), gpa_id, enc, data, sysmap),
            gpa_id.memid.is_sm(memid) ==> old_pt.spec_ram().gpmemop_requires(
                MemOp::Write(gpa_id, enc, data),
                sysmap,
            ),
        ensures
            new_pt.inv(memid),
    {
        reveal(GuestPTRam::inv_dom_ok);
        reveal(GuestPTRam::inv_content_ok);
        reveal(VRamDB::op);
        reveal(VRamDB::op_write);
        let rmp = old_pt.spec_ram().spec_rmp();
        let op_memid = gpa_id.memid;
        let memop = MemOp::Write(gpa_id, enc, data);
        assert(rmp === new_pt.spec_ram().spec_rmp());
        assert(new_pt.ram.rmp.dom() === old_pt.ram.rmp.dom());
        assert(new_pt.inv_dom_ok(memid)) by {
            old_pt.spec_ram().proof_op_inv(sysmap, memop);
            assert(new_pt.spec_ram().inv());
        }
        assert(new_pt.inv_for_identity_map_ok(memid)) by {
            reveal(GuestPTRam::inv_for_identity_map_ok);
            assert forall|gvn: GVN|
                gvn.is_valid() && new_pt.map_entry_ok(memid, gvn, MAX_PT_LEVEL).is_Some() implies (
            #[trigger] new_pt.map_entry_ok(
                memid,
                gvn,
                MAX_PT_LEVEL,
            )).get_Some_0().spec_ppn().value() === gvn.value() by {
                Self::lemma_write_pte_inv_ppn_enc(
                    old_pt,
                    new_pt,
                    sysmap,
                    memid,
                    memop,
                    gvn,
                    MAX_PT_LEVEL,
                );
                assert(old_pt.map_entry_ok(memid, gvn, MAX_PT_LEVEL).get_Some_0().spec_ppn().value()
                    === gvn.value());
            }
        }
        assert(new_pt.inv_encrypted_priv_mem_ok(memid)) by {
            reveal(GuestPTRam::inv_encrypted_priv_mem_ok);
            assert forall|gvn: GVN|
                gvn.is_valid() && (new_pt.need_c_bit(memid, gvn) && new_pt.map_entry_ok(
                    memid,
                    gvn,
                    MAX_PT_LEVEL,
                ).is_Some()) implies #[trigger] new_pt.map_entry_ok(
                memid,
                gvn,
                MAX_PT_LEVEL,
            ).get_Some_0().is_encrypted() by {
                let pte_gpa = new_pt.map_entry_gpa_ok(memid, gvn, MAX_PT_LEVEL).get_Some_0();
                Self::lemma_write_pte_inv_ppn_enc(
                    old_pt,
                    new_pt,
                    sysmap,
                    memid,
                    memop,
                    gvn,
                    MAX_PT_LEVEL,
                );
                assert(old_pt.map_entry_ok(memid, gvn, MAX_PT_LEVEL).get_Some_0().is_encrypted())
            }
        }
        assert forall|gvn: GVN| gvn.is_valid() implies #[trigger] new_pt.inv_content_gpa_ok(
            memid,
            gvn,
        ) by {
            assert forall|lvl: PTLevel|
                !lvl.is_L0() && (#[trigger] new_pt.map_entry_ok(
                    memid,
                    gvn,
                    lvl,
                )).is_Some() implies memtype(
                memid,
                new_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn(),
            ).is_pt(lvl.child_lvl().get_Some_0()) by {
                Self::lemma_write_pte_inv_ppn_enc(old_pt, new_pt, sysmap, memid, memop, gvn, lvl);
                assert(old_pt.map_entry_ok(memid, gvn, lvl).is_Some());
                assert(old_pt.inv_content_gpa_ok(memid, gvn));
                assert(memtype(
                    memid,
                    old_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn(),
                ).is_pt(lvl.child_lvl().get_Some_0()));
                assert(old_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn()
                    === new_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn());
            }
        }
        assert(new_pt.spec_ram().inv_sw(memid));
    }

    pub proof fn lemma_pgtb_walk_addrs_recursive_any_sysmap(
        &self,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
        sysmap: SysMap,
    )
        requires
            self.pgtb_walk_addrs_recursive(sysmap, memid, gvn, lvl).is_Some(),
            self.spec_ram().inv_sw(memid),
            gvn.is_valid(),
        ensures
            self.pgtb_walk_addrs_recursive(sysmap, memid, gvn, lvl)
                === self.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl),
        decreases lvl.as_int(),
    {
        reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive, 1);
        let rmp = self.spec_ram().spec_rmp();
        let vram = self.spec_ram();
        let sram = self.spec_ram().spec_sram();
        match lvl.parent_lvl() {
            Option::None => {
                assert(self.pgtb_walk_addrs_recursive(sysmap, memid, gvn, lvl)
                    === self.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl));
            },
            Option::Some(next_lvl) => {
                self.lemma_pgtb_walk_addrs_recursive_any_sysmap(memid, gvn, next_lvl, sysmap);
                let next_pte_gpmem = self.pgtb_walk_addrs_recursive(sysmap, memid, gvn, next_lvl);
                assert(next_pte_gpmem.is_Some());
                let next_pte_gpmem = next_pte_gpmem.get_Some_0();
                self.lemma_map_entry_gpa_valid(sysmap, memid, gvn, next_lvl);
                vram.lemma_read_enc_byte_ok(
                    sysmap,
                    AddrMemID { range: next_pte_gpmem, memid },
                    true,
                );
            },
        }
    }

    pub proof fn lemma_map_entry_gpa_model1_eq(
        &self,
        other: &Self,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    )
        requires
            other.inv(memid),
            gvn.is_valid(),
            rmp_inv_sw(&other.spec_ram().spec_rmp(), memid),
            rmp_inv_memid_int(&other.spec_ram().spec_rmp(), memid),
            self.model1_eq(other, memid),
        ensures
            self.map_entry_gpa_ok(memid, gvn, lvl).is_Some() ==> self.map_entry_gpa_ok(
                memid,
                gvn,
                lvl,
            ) === other.map_entry_gpa_ok(memid, gvn, lvl),
            other.map_entry_gpa_ok(memid, gvn, lvl).is_None() ==> self.map_entry_gpa_ok(
                memid,
                gvn,
                lvl,
            ).is_None(),
        decreases lvl.as_int(),
    {
        reveal_with_fuel(GuestPTRam::pgtb_walk_addrs_recursive_ok, 1);
        match lvl.parent_lvl() {
            Option::None => {
                assert(self.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl)
                    === other.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl));
            },
            Option::Some(next_lvl) => {
                self.lemma_map_entry_gpa_model1_eq(other, memid, gvn, next_lvl);
                let next_pte_gpmem = self.pgtb_walk_addrs_recursive_ok(memid, gvn, next_lvl);
                if next_pte_gpmem.is_Some() {
                    let next_pte_gpmem = next_pte_gpmem.get_Some_0();
                    assert(memtype(memid, next_pte_gpmem.to_page()).is_sm_int()) by {
                        other.lemma_map_entry_gpa_is_pte_type(memid, gvn, next_lvl);
                    }
                    self.lemma_map_entry_gpa_ok_valid(memid, gvn, next_lvl);
                    self.spec_ram().lemma_read_enc_ok_model1_eq(
                        &other.spec_ram(),
                        AddrMemID { range: next_pte_gpmem, memid },
                    );
                } else {
                    //assert(self.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl) === other.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl));
                }
            },
        }
    }

    pub proof fn lemma_map_entry_model1_eq(
        &self,
        other: &Self,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    )
        requires
            other.inv(memid),
            gvn.is_valid(),
            rmp_inv_sw(&other.spec_ram().spec_rmp(), memid),
            rmp_inv_memid_int(&other.spec_ram().spec_rmp(), memid),
            self.model1_eq(other, memid),
        ensures
            self.map_entry_ok(memid, gvn, lvl).is_Some() ==> self.map_entry_ok(memid, gvn, lvl)
                === other.map_entry_ok(memid, gvn, lvl),
            other.map_entry_ok(memid, gvn, lvl).is_None() ==> self.map_entry_ok(
                memid,
                gvn,
                lvl,
            ).is_None(),
    {
        self.lemma_map_entry_gpa_model1_eq(other, memid, gvn, lvl);
        let pte_gpa = self.map_entry_gpa_ok(memid, gvn, lvl);
        let pte_gpa2 = other.map_entry_gpa_ok(memid, gvn, lvl);
        if self.map_entry_ok(memid, gvn, lvl).is_Some() {
            self.lemma_map_entry_gpa_ok_valid(memid, gvn, lvl);
            assert(pte_gpa.is_Some());
            assert(pte_gpa === pte_gpa2);
            let pte_gpa = pte_gpa.get_Some_0();
            let pte_gpa2 = pte_gpa2.get_Some_0();
            assert(memtype(memid, pte_gpa2.to_page()).is_PTE()) by {
                other.lemma_map_entry_gpa_is_pte_type(memid, gvn, lvl);
            }
            self.spec_ram().lemma_read_enc_ok_model1_eq(
                &other.spec_ram(),
                AddrMemID { range: pte_gpa, memid },
            );
        }
    }

    pub proof fn lemma_map_entry_gpa_any_sysmap(
        &self,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
        sysmap: SysMap,
    )
        requires
            gvn.is_valid(),
            self.map_entry_gpa(sysmap, memid, gvn, lvl).is_Some(),
            self.spec_ram().inv_sw(memid),
        ensures
            self.map_entry_gpa(sysmap, memid, gvn, lvl) === self.map_entry_gpa_ok(memid, gvn, lvl),
        decreases lvl.as_int(),
    {
        self.lemma_pgtb_walk_addrs_recursive_any_sysmap(memid, gvn, lvl, sysmap);
    }

    pub proof fn lemma_map_entry_any_sysmap(
        &self,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
        sysmap: SysMap,
    )
        requires
            gvn.is_valid(),
            self.map_entry(sysmap, memid, gvn, lvl).is_Some(),
            self.spec_ram().inv_sw(memid),
        ensures
            self.map_entry(sysmap, memid, gvn, lvl) === self.map_entry_ok(memid, gvn, lvl),
        decreases lvl.as_int(),
    {
        self.lemma_pgtb_walk_addrs_recursive_any_sysmap(memid, gvn, lvl, sysmap);
        let pte_gpa = self.map_entry_gpa(sysmap, memid, gvn, lvl);
        let pte_gpa_ok = self.map_entry_gpa_ok(memid, gvn, lvl);
        assert(pte_gpa.is_Some());
        assert(pte_gpa_ok === pte_gpa);
        let pte_gpa = pte_gpa.get_Some_0();
        self.lemma_map_entry_gpa_ok_valid(memid, gvn, lvl);
        self.spec_ram().lemma_read_enc_byte_ok(sysmap, AddrMemID { range: pte_gpa, memid }, true);
    }
}

} // verus!
