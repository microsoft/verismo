use super::*;
use crate::arch::attack::*;
verus! {
    impl MemDB
    {
        pub open spec fn to_gpop_ok(&self, memop: MemOp<GuestVir>) -> MemOp<GuestPhy>
        {
            let gvmem = memop.to_mem();
            let op_memid = memop.to_memid();
            let guestmap = self.to_mem_map_ok(op_memid);
            let gpmem = gvmem.convert(
                guestmap.translate(gvmem.to_page()).get_Some_0()
            );
            let enc = guestmap.is_encrypted(gvmem.to_page());
            memop.translate_gpn(gpmem, enc.get_Some_0())
        }

        pub open spec fn vop_requires(&self, memop: MemOp<GuestVir>) -> bool
        {
            let gvn = memop.to_page();
            let gp_memop = self.to_gpop_ok(memop);
            let gmap = self.to_mem_map_ok(memop.to_memid());
            let sysmap = self.spec_sysmap()[memop.to_memid()];
            if gmap.translate(gvn).is_Some() {
                self.spec_vram().gpmemop_requires(gp_memop, sysmap)
            } else {
                true
            }
        }

        // No sysmap dependency
        pub open spec fn inv(&self, memid: MemID) -> bool
        {
            &&& self.spec_g_page_table(memid).inv(memid)
            &&& self.to_mem_map_ok(memid).is_identity_map()
            &&& self.spec_tlb().inv_encrypted_priv_mem(memid)
            &&& self.spec_vram().inv()
            &&& self.spec_vram().inv_sw(memid)
            &&& memid.is_Guest()
        }

        pub open spec fn to_mem_map_ok(&self, memid: MemID) -> MemMap<GuestVir, GuestPhy>
        {
            MemMap {
                db: self.spec_g_page_table(memid).to_mem_map_ok(memid).db.union_prefer_right
                (self.spec_tlb().to_mem_map(memid).db)
            }
        }
    }
}

verus! {
    impl Model1Eq for MemDB {
        open spec fn model1_eq(&self, other: &Self, memid: MemID) -> bool {
            self.spec_vram().model1_eq(&other.spec_vram(), memid)
                && self.spec_tlb().model1_eq(&other.spec_tlb(), memid)
                && equal(
                    self.l0_entry.spec_index(memid),
                    other.l0_entry.spec_index(memid),
                )
        }
    }

    impl Model2Eq for MemDB {
        open spec fn model2_eq(&self, other: &Self) -> bool {
            self.spec_vram().model2_eq(&other.spec_vram())
                && self.spec_tlb().model2_eq(&other.spec_tlb())
                && equal(self.l0_entry, other.l0_entry)
        }
    }
}
