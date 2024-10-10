use super::*;
verus! {

impl GuestPTRam {
    #[verifier(opaque)]
    // Returns the GPA of a page table entry for translating a page gvn.
    pub open spec fn pgtb_walk_addrs_recursive(
        &self,
        sysmap: SysMap,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    ) -> Option<GPMem>
        decreases lvl.as_int(),
    {
        let l0_entry = self.l0_entry(memid);
        let next_opt = lvl.parent_lvl();
        let idx = lvl.spec_table_index(gvn.to_addr()) as nat;
        if next_opt.is_None() {
            Option::Some(GPMem::from_range(l0_entry.addr_for_idx(idx), PT_ENTRY_SIZE as nat))
        } else {
            let next_lvl = next_opt.get_Some_0();
            if next_lvl.as_int() < lvl.as_int() {
                let next_pte_addrs = self.pgtb_walk_addrs_recursive(sysmap, memid, gvn, next_lvl);
                if next_pte_addrs.is_Some() {
                    let next_pte_gpa = next_pte_addrs.get_Some_0();
                    let next_pte = self.hw_read_pte(memid, sysmap, next_pte_gpa);
                    if next_pte.is_Some() && self.valid_access(memid, next_pte_gpa, sysmap) {
                        Option::Some(
                            GPMem::from_range(
                                next_pte.get_Some_0().addr_for_idx(idx),
                                PT_ENTRY_SIZE as nat,
                            ),
                        )
                    } else {
                        Option::None
                    }
                } else {
                    Option::None
                }
            } else {  // unreachable
                Option::None
            }
        }
    }

    /// Hardware read the data from spa without checking RMP.
    pub open spec fn hw_read_pte(&self, memid: MemID, sysmap: SysMap, gpa: GPMem) -> Option<
        SpecGuestPTEntry,
    > {
        let val = self.ram.get::<GuestPTEntry>(AddrMemID { range: gpa, memid }, true, sysmap);
        Option::Some(
            val@,
        )
        //Option::Some(ByteStream::to_data(self.spec_ram().spec_ret_bytes(MemOp::Read(AddrMemID{range: gpa, memid}, true), sysmap)))

    }

    pub open spec fn map_entry_gpa(
        &self,
        sysmap: SysMap,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    ) -> Option<GPMem> {
        self.pgtb_walk_addrs_recursive(sysmap, memid, gvn, lvl)
    }

    pub open spec fn map_entry(
        &self,
        sysmap: SysMap,
        memid: MemID,
        gvn: GVN,
        lvl: PTLevel,
    ) -> Option<SpecGuestPTEntry> {
        let pte_gpa = self.map_entry_gpa(sysmap, memid, gvn, lvl);
        if pte_gpa.is_Some() && self.valid_access(memid, pte_gpa.get_Some_0(), sysmap) {
            self.hw_read_pte(memid, sysmap, pte_gpa.get_Some_0())
        } else {
            Option::None
        }
    }

    #[verifier(opaque)]
    pub open spec fn valid_translate(&self, sysmap: SysMap, memid: MemID, gvn: GVN) -> bool {
        &&& self.map_entry(sysmap, memid, gvn, PTLevel::L0).is_Some()
        &&& (forall|lvl|
            self.valid_access(
                memid,
                (#[trigger] self.map_entry_gpa(sysmap, memid, gvn, lvl)).get_Some_0(),
                sysmap,
            ))
    }

    // pt_rmp: is a RMP table with only spa whose gpa is of PTE type.
    pub open spec fn to_mem_map(&self, sysmap: SysMap, memid: MemID) -> MemMap<GuestVir, GuestPhy> {
        let map = Map::new(
            |gvn: GVN| gvn.is_valid() && self.map_entry(sysmap, memid, gvn, PTLevel::L0).is_Some(),
            |gvn: GVN| self.map_entry(sysmap, memid, gvn, PTLevel::L0).get_Some_0(),
        );
        MemMap { db: map }
    }

    pub open spec fn gpn_is_encrypted(&self, sysmap: SysMap, gvn: GVN, memid: MemID) -> bool {
        self.map_entry(sysmap, memid, gvn, PTLevel::L0).get_Some_0().is_encrypted()
    }
}

} // verus!
