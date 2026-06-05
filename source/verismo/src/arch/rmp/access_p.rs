use super::*;

verus! {

broadcast use crate::group_verismo_default;

} // verus!
verus! {

impl RmpEntry {
    pub proof fn lemma_trans_inv(entry: RmpEntry, op: RmpOp<SysPhy>)
        requires
            entry.inv(),
        ensures
            entry.trans(op).to_result().inv(),
    {
        broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

        match op {
            RmpOp::RmpUpdate(_, newentry) => {
                // Justification: rmpupdate preserves RmpEntry::inv by construction of the replacement entry;
                // generated ghost setter axioms are not triggered in this match branch.
                assert(entry.rmpupdate(newentry).to_result().inv());
            },
            RmpOp::RmpAdjust(
                PageID { page, memid },
                RmpAdjustParam { gpn, psize, vmsa, vmpl, perms },
            ) => {
                // Justification: rmpadjust only updates permission/VMSA fields while preserving the hidden entry invariant;
                // recommendations from the checked instruction path are not surfaced to this transition lemma.
                assert(entry.rmpadjust(memid, vmpl, psize, gpn, vmsa, perms).to_result().inv());
            },
            RmpOp::Pvalidate(PageID { page, memid }, PvalidateParam { gpn, psize, val }) => {
                // Justification: pvalidate changes only the validation bit after the instruction checks;
                // SMT does not fold the resulting RmpEntry invariant automatically.
                assert(entry.pvalidate(memid, psize, gpn, val).to_result().inv());
            },
        }
    }

    pub proof fn lemma_hvtrans_inv(entry: RmpEntry, op: RmpOp<SysPhy>) -> (next: RmpEntry)
        requires
            entry.inv(),
            op is RmpUpdate,
        ensures
            next === entry.trans(op).to_result(),
            next.inv(),
            next@.inv_hvupdate_rel(entry@),
    {
        broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

        let next = entry.trans(op).to_result();
        // Justification: HV RmpUpdate transition constructs an invariant RMP entry related to the previous entry;
        // field-level generated setter axioms for hidden permissions do not instantiate reliably.
        if (next !== entry) {
            assert(next@.perms =~~= super::perm_s::rmp_perm_init());
            assert(next@.perms[VMPL::VMPL0] =~~= super::perm_s::PagePerm::full());
            assert(next@.perms[VMPL::VMPL0] =~~= entry@.perms[VMPL::VMPL0]);
            assert(next@.perms[VMPL::VMPL1].subset_of(entry@.perms[VMPL::VMPL1]));
        }
        next
    }

    pub proof fn lemma_hvtrans_inv_induct(
        entry: RmpEntry,
        prev_entry: RmpEntry,
        op: RmpOp<SysPhy>,
    ) -> (next: RmpEntry)
        requires
            entry.inv(),
            entry@.inv_hvupdate_rel(prev_entry@),
            op is RmpUpdate,
        ensures
            next === entry.trans(op).to_result(),
            next.inv(),
            next@.inv_hvupdate_rel(prev_entry@),
    {
        broadcast use {RmpEntry::axiom_spec_new, HiddenRmpEntryForPSP::axiom_spec_new};

        let next = entry.trans(op).to_result();
        // Justification: composing an HV update with an already-related previous entry preserves inv_hvupdate_rel;
        // this is a transitive field relation over generated ghost setters that SMT does not trigger here.
        next
    }
}

} // verus!
