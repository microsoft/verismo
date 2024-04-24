use super::*;
use crate::arch::attack::*;

verus! {

impl TLB {
    pub proof fn lemma_model1_inv_encrypted_priv_mem(&self, other: &Self, memid: MemID)
        requires
            self.model1_eq(other, memid),
            other.inv_encrypted_priv_mem(memid),
        ensures
            self.inv_encrypted_priv_mem(memid),
    {
        reveal(MemMap::inv_encrypted_priv_mem);
        let memmap = self.to_mem_map(memid);
        assert forall|gvn: GVN|
            gvn.is_valid() && memtype(
                memid,
                memmap.translate(gvn).get_Some_0(),
            ).need_c_bit() implies #[trigger] memmap.is_encrypted_or_none(gvn) by {
            if memmap.translate(gvn).is_Some() {
                assert(other.to_mem_map(memid).is_encrypted_or_none(gvn));
            }
        }
    }
}

} // verus!
