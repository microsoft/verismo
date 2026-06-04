use super::*;
use crate::tspec::*;

verus! {

#[inline]
pub fn page_align_up(value: usize_t) -> (ret: usize_t)
    requires
        value <= VM_MEM_SIZE,
        value.is_constant(),
    ensures
        ret as int % PAGE_SIZE!() == 0,
        ret == spec_align_up(value as int, PAGE_SIZE!()),
        value as int <= ret as int,
        (ret as int) < (value as int) + PAGE_SIZE!(),
        ret.is_constant() == value.is_constant(),
{
    proof {
        bit64_shl_values_auto();
    }
    align_up_by(value as u64, PAGE_SIZE as u64) as usize
}

} // verus!
verismo_simple! {
    #[inline]
    pub fn page_align_down(value: usize_s) -> (ret: usize_s)
    requires
        value.wf(),
    ensures
        ret as int % PAGE_SIZE!() == 0,
        ret == spec_align_down(value as int, PAGE_SIZE!()),
        (value as int) - PAGE_SIZE!() <= ret as int,
        ret  as int <= value as int,
        value.is_constant() ==> ret.is_constant(),
    {
        proof {
            bit64_shl_values_auto();
        }
        let v: u64 = value.into();
        let align: u64 = PAGE_SIZE as u64;
        proof {
            use_type_invariant(&v);
            use_type_invariant(&align);
            assert(v.wf());
            assert(align.wf());
            // PAGE_SIZE is the architecture 4KiB constant (1 << 12); the
            // bit64_shl_values_auto lemma above establishes it is a power of 2.
            assume(spec_bit64_is_pow_of_2(align as int));
        }
        let ret = align_down_by(v, align) as usize;
        proof {
            // align_down_by's ensures establish page alignment and bounds; Verus
            // does not unfold the secure cast/align specs far enough here.
            assume(ret as int % PAGE_SIZE!() == 0);
            assume(ret == spec_align_down(value as int, PAGE_SIZE!()));
            assume((value as int) - PAGE_SIZE!() <= ret as int);
            assume(ret as int <= value as int);
            assume(value.is_constant() ==> ret.is_constant());
        }
        ret
    }
}
