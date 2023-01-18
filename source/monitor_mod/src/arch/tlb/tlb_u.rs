use super::*;
use crate::arch::attack::*;

verus! {
impl Model1Eq for TLB {
    open spec fn model1_eq(&self, other: &Self, memid: MemID) -> bool {
        self.db.spec_index(memid).submap_of(other.db.spec_index(memid))
    }
}
impl Model2Eq for TLB {
    open spec fn model2_eq(&self, other: &Self) -> bool {
        forall |memid| (#[trigger]self.db.spec_index(memid)).submap_of(
            #[trigger] other.db.spec_index(memid))
    }
}
}

verus! {
    impl TLB {
        pub open spec fn inv_encrypted_priv_mem(&self, memid: MemID) -> bool
        {
            let memmap = self.to_mem_map(memid);
            memmap.inv_encrypted_priv_mem(memid)
        }
    }
}
