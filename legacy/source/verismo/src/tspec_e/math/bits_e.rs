use super::bits_p::*;
use super::*;
use crate::tspec::*;

verus! {

pub fn bit_check(val: u64, bit: u64) -> (ret: bool)
    requires
        bit < 64,
    ensures
        ret == spec_has_bit_set(val as u64, bit as u64),
{
    proof {
        lemma_bits64!();
    }
    val & (1u64 << bit) != 0
}

} // verus!
verismo! {
    pub fn bit_set(val: &mut u64, bit: u64)
    requires
        bit < 64,
    ensures
        *val == spec_bit_set(*old(val) as u64, bit as u64),
        spec_has_bit_set(*val as u64, bit as u64),
    {
        proof{
            proof_bit64_clear_set_property(*val as u64, bit as u64);
        }
        *val = *val | (1u64 << bit)
    }

    pub fn bit_clear(val: &mut u64, bit: u64)
    requires
        bit < 64,
    ensures
        *val == spec_bit_clear((*old(val)) as u64, bit as u64),
        !spec_has_bit_set((*val) as u64, bit as u64),
        //(*val)@ === ((*old(val)) & (!(1u64_s << bit)))@
    {
        proof{
            proof_bit64_clear_set_property((*val) as u64, bit as u64);
        }
        *val = (*val) & (!(1u64_s << bit))
    }

    pub open spec fn spec_u32_to_u64(low: int, high: int) -> int
    {
        low + high * 0x1_0000_0000
    }

    pub open spec fn spec_u64_highu32(value: int) -> int
    {
        value / 0x1_0000_0000
    }

    #[inline]
    pub fn u32_to_u64(low: u32, high: u32) -> (ret: u64)
    ensures
        ret as int == spec_u32_to_u64(low as int, high as int)
    {
        proof {
            bit64_shl_values_auto();
            bit64_shl_mul_rel(high as u64, 32);
        }
        let low = low as u64;
        let high = high as u64;
        low  + (high << 32u64)
    }

    #[inline]
    pub fn u64_highu32(value: u64) -> (ret: u32)
    ensures
        ret as int == spec_u64_highu32(value as int)
    {
        proof {
            bit64_shr_div_rel(value as u64, 32);
            bit64_shl_values_auto();
        }
        (value >> 32u64) as u32
    }

    pub fn fill_tailing_ones(input: u64) -> (ret: u64)
    ensures
        ret == spec_fill_ones_exe(input as u64),
    {
        let mut ret = input;
        ret = ret | (ret >> 1u64);
        ret = ret | (ret >> 2u64);
        ret = ret | (ret >> 4u64);
        ret = ret | (ret >> 8u64);
        ret = ret | (ret >> 16u64);
        ret = ret | (ret >> 32u64);
        ret
    }
}

verus! {

pub fn prev_power_of_two(input: u64) -> (ret: u64)
    ensures
        spec_is_prev_power_of_two(input as nat, ret as nat),
{
    proof {
        lemma_prev_power_of_two(input as u64);
    }
    if input == 0 {
        0
    } else {
        proof {
            lemma_fill_ones(input as u64);
        }
        let mut ret: u64 = fill_tailing_ones(input.into()).into();
        ret = (ret >> 1u64) + 1u64;
        ret
    }
}

pub fn next_power_of_two(input: u64) -> (ret: u64)
    requires
        input <= POW2!(63),
    ensures
        spec_is_next_power_of_two(input as nat, ret as nat),
{
    proof {
        lemma_next_power_of_two(input as u64);
    }
    if input <= 1 {
        1
    } else {
        let v = input - 1;
        proof {
            lemma_fill_ones(v as u64);
        }
        fill_tailing_ones(v.into()).reveal_value() + 1
    }
}

} // verus!
