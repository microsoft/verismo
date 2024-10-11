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
        assert(v.wf());
        (align_down_by(v, PAGE_SIZE as u64) as usize)
    }
}
