use super::*;

verus! {
    impl RmpEntry {
        pub proof fn lemma_trans_inv(entry: RmpEntry, op: RmpOp<SysPhy>)
        requires
            entry.inv(),
        ensures
            entry.trans(op).to_result().inv(),
        {
            match op {
                RmpOp::RmpUpdate(_, newentry) => {
                    assert(entry.rmpupdate(newentry).to_result().inv());
                }
                RmpOp::RmpAdjust(PageID {page, memid}, RmpAdjustParam {gpn, psize, vmsa, vmpl, perms}) => {
                    assert(entry.rmpadjust(memid, vmpl, psize, gpn, vmsa, perms).to_result().inv());
                }
                RmpOp::Pvalidate(PageID {page, memid}, PvalidateParam {gpn, psize, val}) => {
                    assert(entry.pvalidate(memid, psize, gpn, val).to_result().inv());
                }
            }
        }

        pub proof fn lemma_hvtrans_inv(entry: RmpEntry, op: RmpOp<SysPhy>) -> (next: RmpEntry)
        requires
            entry.inv(),
            op.is_RmpUpdate(),
        ensures
            next === entry.trans(op).to_result(),
            next.inv(),
            next@.inv_hvupdate_rel(entry@),
        {
            let next = entry.trans(op).to_result();
            if(next !== entry) {
                assert(next@.perms =~~= super::perm_s::rmp_perm_init());
                assert(next@.perms[VMPL::VMPL0] =~~= super::perm_s::PagePerm::full());
                assert(next@.perms[VMPL::VMPL0] =~~= entry@.perms[VMPL::VMPL0]);
                assert(next@.perms[VMPL::VMPL1].subset_of(entry@.perms[VMPL::VMPL1]));
            }
            next
        }

        pub proof fn lemma_hvtrans_inv_induct(entry: RmpEntry, prev_entry: RmpEntry, op: RmpOp<SysPhy>) -> (next: RmpEntry)
        requires
            entry.inv(),
            entry@.inv_hvupdate_rel(prev_entry@),
            op.is_RmpUpdate()
        ensures
            next === entry.trans(op).to_result(),
            next.inv(),
            next@.inv_hvupdate_rel(prev_entry@),
        {
            entry.trans(op).to_result()
        }
    }
}
