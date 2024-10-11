use super::*;

verus! {

pub proof fn proof_bits_to_pow2(bit: u64)
    requires
        0 <= bit < 64,
    ensures
        (1u64 << bit) as int == spec_nat_pow2(bit as nat),
    decreases bit,
{
    if bit > 0 {
        let bit2 = sub(bit, 1);
        proof_bits_to_pow2(bit2);
        let val2: u64 = (1u64 << bit2);
        assert(val2 == spec_nat_pow2(bit2 as nat));
        assert(bit2 <= 62);
        assert((1u64 << bit2) <= (1u64 << 62u64)) by (bit_vector)
            requires
                bit2 <= 62,
        ;
        assert((1u64 << 62) == POW2!(62)) by (bit_vector);
        assert((1u64 << sub(bit, 1)) << 1u64 == (1u64 << bit)) by (bit_vector)
            requires
                0 < bit < 64,
        ;
        assert(val2 << 1u64 == mul(2u64, val2)) by (bit_vector)
            requires
                val2 <= 0x4000_0000_0000_0000u64,
        ;
        assert(spec_nat_pow2(bit as nat) == mul(2, (1u64 << bit2)));
    } else {
        assert((1u64 << 0) == 1) by (bit_vector);
    }
}

pub open spec fn spec_is_power_of_2(val: nat) -> bool {
    exists|bit: u64| val == (1u64 << bit)
}

pub open spec fn spec_pow2_to_bits_exe(val: nat) -> nat
    recommends
        val as u64 == val,
        val != 0,
    decreases val,
{
    let val64 = val as u64;
    if val > 1 {
        if val64 >> 1u64 < val64 {
            spec_pow2_to_bits_exe((val64 >> 1u64) as nat) + 1
        } else {
            0
        }
    } else {
        0
    }
}

pub proof fn proof_pow2_to_bits(val: nat) -> (ret: u64)
    requires
        val as u64 == val,
        val != 0,
    ensures
        ret == spec_pow2_to_bits_exe(val),
        ret < 64,
        (1u64 << ret) <= val,
        val < (1u64 << ret) * 2,
        (spec_bit64_is_pow_of_2(val as int) && val > 1) ==> spec_bit64_is_pow_of_2(
            (val as u64 >> 1u64) as int,
        ),
        spec_bit64_is_pow_of_2(val as int) ==> ret == spec_pow2_to_bits(val as u64),
    decreases val,
{
    bit64_shl_values_auto();
    let val64 = val as u64;
    let ret = spec_pow2_to_bits_exe(val);
    if spec_bit64_is_pow_of_2(val64 as int) && val > 1 {
        assert(spec_bit64_is_pow_of_2((val64 >> 1u64) as int)) by (bit_vector)
            requires
                spec_bit64_is_pow_of_2(val64 as int),
                val64 > 1,
        ;
    }
    if val > 1 {
        let next = val64 >> 1u64;
        assert(next < val64 && next < (1u64 << 63) && next > 0) by (bit_vector)
            requires
                next == val64 >> 1u64,
                val64 > 1,
        ;
        let next_bits = spec_pow2_to_bits_exe(next as nat);
        proof_pow2_to_bits(next as nat);
        assert(next_bits < 63);
        assert(ret < 64);
        let next_bits64 = next_bits as u64;
        let ret_bits64 = next_bits64 + 1;
        bit64_shr_div_rel(val64, 1);
        return ret as u64;
    } else {
        return 0;
    }
}

} // verus!
