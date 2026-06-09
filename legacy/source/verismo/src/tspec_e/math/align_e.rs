use super::align_s::*;
use super::*;

verus! {

pub fn align_up_by(val: u64, align: u64) -> (ret: u64)
    requires
        spec_bit64_is_pow_of_2(align as int),
        val + align <= u64::MAX,
    ensures
        (ret as int) % (align as int) == 0,
        ret as int == spec_align_up(val as int, align as int),
        spec_is_align_up_by_int(val as int, align as int, ret as int),
{
    proof {
        proof_align_up(val as nat, align as nat);
        proof_align_is_aligned(val as int, align as int);
    }
    let mask = align - 1;
    if val & mask == 0 {
        val
    } else {
        (val | mask) + 1
    }
}

} // verus!
verismo_simple! {
    pub fn align_down_by(val: u64, align: u64) -> (ret: u64)
        requires
            spec_bit64_is_pow_of_2(align as int),
            val.wf(),
            align.wf(),
        ensures
            ret == spec_align_down(val as int, align as int),
            spec_is_align_down_by_int(val as int, align as int, ret as int),
            (ret as int) == val as int - val as int % align as int,
            ret as int == (val as u64 >> spec_pow2_to_bits(align as u64)) << spec_pow2_to_bits(align as u64),
            (ret as int) % (align as int) == 0,
            val.is_constant() && align.is_constant() ==> ret.is_constant(),
            ret.wf(),
    {
        proof {
            proof_align_down(val as nat, align as nat);
            proof_align_is_aligned(val as int, align as int);
        }
        val & (!(align - 1))
    }
}
