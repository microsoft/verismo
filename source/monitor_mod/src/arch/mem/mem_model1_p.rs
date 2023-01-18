use super::*;
use crate::arch::attack::*;

verus! {
impl MemDB{
    #[verifier(external_body)]
    pub proof fn proof_model1_content_integrity(&self, old_memdb: &MemDB, memid: MemID, memop: MemOp<GuestVir>)
    requires
        memop.is_Read(),
        old_memdb.inv(memid),
        self.model1_eq(old_memdb, memid),
        self.op(memop).is_Ok(),
        self.to_mem_map(memid).is_encrypted_or_none(memop.to_page())
    ensures
        self.ret(memop) === old_memdb.ret(memop),
    {
    }
    pub proof fn proof_model1_pgram_inv(&self, old_memdb: &MemDB, memid: MemID)
    requires
        old_memdb.inv(memid),
        self.model1_eq(old_memdb, memid),
    ensures
        self.spec_g_page_table(memid).inv(memid),
    {
        reveal(GuestPTRam::inv_dom_ok);
        reveal(GuestPTRam::inv_content_ok);
        self.spec_vram().lemma_model_eq_inv(&old_memdb.spec_vram(), memid);
        let new_pt = self.spec_g_page_table(memid);
        let old_pt = old_memdb.spec_g_page_table(memid);
        assert (new_pt.inv_dom_ok(memid));

        assert forall |gvn: GVN| gvn.is_valid()
        implies
            #[trigger] new_pt.inv_content_gpa_ok(memid, gvn)
        by{
            assert forall |lvl: PTLevel|
                (!lvl.is_L0() && (#[trigger]new_pt.map_entry_ok(memid, gvn, lvl)).is_Some())
            implies
                memtype(memid, new_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn()).is_pt(lvl.child_lvl().get_Some_0())
            by {
                new_pt.lemma_map_entry_model1_eq(&old_pt, memid, gvn, lvl);
                assert(old_pt.map_entry_ok(memid, gvn, lvl).is_Some());
                assert(old_pt.inv_content_gpa_ok(memid, gvn));
                assert(memtype(memid, old_pt.map_entry_ok(memid, gvn, lvl).get_Some_0().spec_ppn()).is_pt(lvl.child_lvl().get_Some_0()));
            }
        }
        assert(new_pt.inv_for_identity_map_ok(memid)) by {
            reveal(GuestPTRam::inv_for_identity_map_ok);
            assert forall |gvn: GVN| gvn.is_valid() &&
                (#[trigger] new_pt.map_entry_ok(memid, gvn, PTLevel::L0)).is_Some()
            implies
                new_pt.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0().spec_ppn().value() === gvn.value()
            by {
                new_pt.lemma_map_entry_model1_eq(&old_pt, memid, gvn, PTLevel::L0);
                assert(old_pt.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0().spec_ppn().value() === gvn.value());
            }
        }
        assert(new_pt.inv_encrypted_priv_mem_ok(memid)) by {
            reveal(GuestPTRam::inv_encrypted_priv_mem_ok);
            assert forall |gvn: GVN|
                (gvn.is_valid()
                && new_pt.need_c_bit(memid, gvn)
                &&  new_pt.map_entry_ok(memid, gvn, PTLevel::L0).is_Some())
            implies
                #[trigger] new_pt.map_entry_ok(memid, gvn, PTLevel::L0).get_Some_0().is_encrypted()
            by {
                new_pt.lemma_map_entry_model1_eq(&old_pt, memid, gvn, PTLevel::L0);
            }
        }
    }
}
}
