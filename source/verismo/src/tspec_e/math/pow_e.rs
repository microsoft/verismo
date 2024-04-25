use super::*;

verus! {

pub fn pow2_to_bits(val: u64) -> (ret: u64)
    requires
        spec_bit64_is_pow_of_2(val as int),
    ensures
        1u64 << (ret as u64) == val as int,
        0 <= (ret as int) < 64,
        ret as u64 == spec_pow2_to_bits(val as u64),
        ret as u64 == spec_pow2_to_bits_exe(val as nat),
{
    proof {
        bit_shl64_auto();
        proof_pow2_to_bits(val as nat);
    }
    if val > 1 {
        let prev = pow2_to_bits(val >> 1u64);
        prev + 1
    } else {
        0
    }
}

} // verus!
