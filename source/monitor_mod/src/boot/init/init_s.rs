use super::*;
use crate::arch::addr_s::VM_MEM_SIZE;
use crate::mem::{RawMemPerms, SnpMemCoreConsole};

verus! {

pub trait InitMem {
    spec fn mem_perms_e820_valid(&self, e820: Seq<E820Entry>) -> bool;

    spec fn mem_perms_e820_invalid(&self, e820: Seq<E820Entry>) -> bool;

    spec fn out_e820_invalidated(&self, e820: Seq<E820Entry>, bound: (int, nat)) -> bool;

    spec fn wf_initial(self, e820: Seq<E820Entry>) -> bool where Self: core::marker::Sized;

    spec fn initmem_wf_basic(self) -> bool where Self: core::marker::Sized;
}

impl InitMem for RawMemPerms {
    open spec fn mem_perms_e820_invalid(&self, e820: Seq<E820Entry>) -> bool {
        &&& self.contains_init_except((0, VM_MEM_SIZE as nat), e820.to_aligned_ranges())
    }

    open spec fn mem_perms_e820_valid(&self, e820: Seq<E820Entry>) -> bool {
        // e820 table records all validated memory.
        &&& forall|r|
            e820.to_aligned_ranges().contains(r) ==> self.contains_default_except(
                r,
                e820.to_valid_ranges(),
            )
    }

    open spec fn out_e820_invalidated(&self, e820: Seq<E820Entry>, bound: (int, nat)) -> bool {
        // contains all memory permission not validated
        forall|r|
            (inside_range(r, bound) && ranges_disjoint(e820.to_aligned_ranges(), r) && r.1 > 0)
                ==> #[trigger] self.contains_range(r) && self.contains_init_mem(r)
    }

    open spec fn wf_initial(self, e820: Seq<E820Entry>) -> bool {
        &&& self.wf()
        &&& self.mem_perms_e820_valid(e820)
    }

    #[verifier(inline)]
    open spec fn initmem_wf_basic(self) -> bool {
        self.wf()
    }
}

pub proof fn lemma_contains_except_remove(
    memperm: RawMemPerms,
    r: (int, nat),
    current_range: (int, nat),
    ranges: Set<(int, nat)>,
    toremove: (int, nat),
)
    requires
        memperm.contains_default_except(current_range, ranges),
        range_disjoint_(r, toremove),
        inside_range(r, current_range),
        ranges.contains(toremove),
    ensures
        memperm.contains_default_except(r, ranges.remove(toremove)),
{
    let newrange = ranges.remove(toremove);
    assert forall|r2|
        (inside_range(r2, r) && ranges_disjoint(newrange, r2) && r2.1
            > 0) implies memperm.contains_default_mem(r2) by {
        assert(ranges_disjoint(newrange.insert(toremove), r2));
        assert(memperm.contains_default_mem(r2));
    }
}

} // verus!
