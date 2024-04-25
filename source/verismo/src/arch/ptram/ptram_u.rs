use super::*;
use crate::arch::attack::*;

verus! {

impl Model1Eq for GuestPTRam {
    open spec fn model1_eq(&self, other: &Self, memid: MemID) -> bool {
        self.spec_ram().model1_eq(&other.spec_ram(), memid) && equal(
            self.l0_entry(memid),
            other.l0_entry(memid),
        )
    }
}

impl Model2Eq for GuestPTRam {
    open spec fn model2_eq(&self, other: &Self) -> bool {
        self.spec_ram().model2_eq(&other.spec_ram()) && equal(self.l0_entry, other.l0_entry)
    }
}

impl GuestPTRam {
    // Returns the GPA of a page table entry for translating a page gvn.
    // To succeed, the sysmap must be consistant with rmp table
    pub open spec fn pgtb_walk_addrs_recursive_ok(
        &self,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    ) -> Option<GPMem> {
        decreases(lvl.as_int());
        let vram = self.spec_ram();
        let rmp = self.spec_ram().spec_rmp();
        let sram = self.spec_ram().spec_sram();
        let l0_entry = self.l0_entry(memid);
        let next_opt = lvl.parent_lvl();
        let idx = AsNat!(lvl.spec_table_index(gvn.to_addr()));
        if next_opt.is_None() {
            Option::Some(GPMem::from_range(l0_entry.addr_for_idx(idx), AsNat!(PT_ENTRY_SIZE!())))
        } else {
            let next_lvl = next_opt.get_Some_0();
            if next_lvl.as_int() < lvl.as_int() {
                let next_pte_addrs = self.pgtb_walk_addrs_recursive_ok(memid, gvn, next_lvl);
                if next_pte_addrs.is_Some() {
                    let next_pte_gpmem = next_pte_addrs.get_Some_0();
                    let next_pte = vram.get_enc_data_ok(AddrMemID { range: next_pte_gpmem, memid });
                    if next_pte.is_Some() {
                        let next_pte: GuestPTEntry = next_pte.get_Some_0();
                        Option::Some(
                            GPMem::from_range(
                                next_pte.view().addr_for_idx(idx),
                                PT_ENTRY_SIZE!() as nat,
                            ),
                        )
                    } else {
                        Option::None
                    }
                } else {
                    Option::None
                }
            } else {
                // unreachable
                Option::None
            }
        }
    }

    pub open spec fn valid_access(&self, memid: MemID, gpa: GPMem, sysmap: SysMap) -> bool {
        self.spec_ram().read_bytes(AddrMemID { range: gpa, memid }, true, sysmap).is_Ok()
    }

    pub open spec fn l0_entry(&self, memid: MemID) -> SpecGuestPTEntry {
        self.l0_entry[memid]
    }

    pub open spec fn inv(&self, memid: MemID) -> bool {
        &&& self.inv_content_ok(memid)
        &&& self.inv_dom_ok(memid)
        &&& self.spec_ram().inv_sw(memid)
        &&& self.spec_ram().inv_memid_int(memid)
        &&& self.spec_ram().inv()
    }

    ///
    /// * If a gpn is PTE type and there is a spa mapped by the gpn, the db should include the ram data at that spa.
    /// * If a gpn (mapping to spa) is not PTE type, db does not contains spa
    pub open spec fn inv_dom_ok(&self, memid: MemID) -> bool {
        //let rmp = self.spec_ram().spec_rmp();
        /*&&& (forall |spn|
                self.ram.dom().contains(spn) === (memtype(memid, (#[trigger]rmp[spn]).view().spec_gpn()).is_PTE() && rmp.dom().contains(spn)))*/
        self.spec_ram().inv()
    }

    pub open spec fn inv_content_gpa_ok(&self, memid: MemID, gvn: GVN) -> bool {
        forall|lvl: PTLevel|
            (!lvl.is_L0() && (#[trigger] self.map_entry_ok(memid, gvn, lvl)).is_Some()) ==> memtype(
                memid,
                self.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn(),
            ).is_pt(lvl.child_lvl().get_Some_0())
    }

    #[verifier(opaque)]
    pub open spec fn inv_content_ok(&self, memid: MemID) -> bool {
        &&& (forall|gvn: GVN| gvn.is_valid() ==> #[trigger] self.inv_content_gpa_ok(memid, gvn))
        &&& self.inv_for_identity_map_ok(memid)
        &&& self.inv_encrypted_priv_mem_ok(memid)
        &&& memtype(memid, self.l0_entry(memid).spec_ppn()).is_pt(PTLevel::L3)
        &&& memid.is_Guest()
    }

    #[verifier(opaque)]
    pub open spec fn inv_for_identity_map_ok(&self, memid: MemID) -> bool {
        &&& (forall|gvn: GVN|
            (gvn.is_valid() && (#[trigger] self.map_entry_ok(memid, gvn, PTLevel::L0)).is_Some())
                ==> self.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0().spec_ppn().value()
                === gvn.value())
    }

    pub open spec fn need_c_bit(&self, memid: MemID, gvn: GVN) -> bool {
        let rmp = self.spec_ram().spec_rmp();
        let entry = self.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0();
        memtype(
            memid,
            entry.spec_ppn(),
        ).need_c_bit()
        //||rmp.has_gpn_memid(entry.spec_ppn(), memid))

    }

    /// Any PTE mapping to private GPN should be marked as encrypted.
    #[verifier(opaque)]
    pub open spec fn inv_encrypted_priv_mem_ok(&self, memid: MemID) -> bool {
        &&& (forall|gvn: GVN|
            (gvn.is_valid() && self.need_c_bit(memid, gvn) && self.map_entry_ok(
                memid,
                gvn,
                PTLevel::L0,
            ).is_Some()) ==> #[trigger] self.map_entry_ok(
                memid,
                gvn,
                PTLevel::L0,
            ).get_Some_0().is_encrypted())
    }

    pub open spec fn map_entry_gpa_ok(&self, memid: MemID, gvn: GVN, lvl: PTLevel) -> Option<
        GPMem,
    > {
        self.pgtb_walk_addrs_recursive_ok(memid, gvn, lvl)
    }

    pub open spec fn map_entry_ok(&self, memid: MemID, gvn: GVN, lvl: PTLevel) -> Option<
        SpecGuestPTEntry,
    > {
        let ret = self.map_entry_exe_ok(memid, gvn, lvl);
        match ret {
            Option::Some(exe_ret) => { Option::Some(exe_ret.view()) },
            _ => Option::None,
        }
    }

    pub open spec fn map_entry_exe_ok(&self, memid: MemID, gvn: GVN, lvl: PTLevel) -> Option<
        GuestPTEntry,
    > {
        let pte_gpa = self.map_entry_gpa_ok(memid, gvn, lvl);
        if pte_gpa.is_Some() {
            let pte_gpa = pte_gpa.get_Some_0();
            let entry = self.spec_ram().get_enc_data_ok::<GuestPTEntry>(
                AddrMemID { range: pte_gpa, memid },
            );
            if entry.is_Some() {
                Option::Some(entry.get_Some_0())
            } else {
                Option::None
            }
        } else {
            Option::None
        }
    }

    pub open spec fn to_mem_map_ok(&self, memid: MemID) -> MemMap<GuestVir, GuestPhy> {
        let map = Map::new(
            |gvn: GVN| gvn.is_valid() && self.map_entry_ok(memid, gvn, PTLevel::L0).is_Some(),
            |gvn: GVN| self.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0(),
        );
        MemMap { db: map }
    }
}

} // verus!
