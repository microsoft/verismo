use super::perm_s::*;
use super::*;

verus! {
    pub open spec fn rmp_op(rmp: &RmpMap, op: RmpOp<SysPhy>) -> ResultWithErr<RmpMap, MemError<RmpOp<SysPhy>>>
    {
        let spn = op.to_page_memid().page;
        if !rmp.dom().contains(spn) {
            ResultWithErr::Error(*rmp, MemError::NestedPF(op))
        } else {
            let newentry = rmp.index(spn).trans(op);
            let new = rmp.insert(spn, newentry.to_result());
            newentry.with_ret(new)
        }
    }

    pub open spec fn rmp_check_access(
        rmp: &RmpMap,
        memid: MemID,
        enc: bool,
        gpmem: GPMem,
        perm: Perm,
        spn: SPN,
    ) -> ResultOrErr<RmpEntry, MemError<()>> {
        let rmpentry: RmpEntry = rmp.index(spn);
        if !rmp.dom().contains(spn) {
            ResultOrErr::Error(MemError::NestedPF(()))
        } else {
            rmpentry.check_access(memid, enc, gpmem, perm)
        }
    }
}
