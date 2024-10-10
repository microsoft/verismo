use vstd::prelude::*;

use super::*;

macro_rules! BIT64 {
    ($x: expr) => {
        (1u64 << (($x) as u64))
    };
}

verus! {
    pub open spec fn has_bit_closure(input: u64) -> spec_fn(u64) -> bool {
        |b: u64| spec_has_bit_set(input, b)
    }

    #[verifier(inline)]
    pub open spec fn has_bits_until(input: u64, nbits: u64, h: u64) -> bool {
        &&& forall |b: u64| (b <= h  && sub(h, b) < nbits) ==> spec_has_bit_set(input, b)
        &&& forall |b: u64| (h < b < 64) ==> !spec_has_bit_set(input, b)
    }

    #[verifier(inline)]
    pub open spec fn nbits_mask(nbits: u64) -> u64
    recommends
        0 < nbits <= 64,
    {
        (sub(BIT64!(sub(nbits, 1)), 1) << 1) | 1u64
    }
}

seq_macro::seq!(N in 0..64 {
    verus!{
    proof fn lemma_zeroval_bits(input: u64)
    requires
        forall |b: u64| 0 <= b < 64 ==> !spec_has_bit_set(input, b)
    ensures
        input == 0
    {
        assert(input == 0 )by(bit_vector)
        requires
            #(
                !spec_has_bit_set(input, N),
            )*
            true;
    }

    proof fn lemma_has_64bits_until_to_mask(val: u64, h: u64)
    requires
        h < 64,
        has_bits_until(val, 64, h),
    ensures
        val == nbits_mask(add(h, 1))
    {
        assert(val == nbits_mask(add(h, 1))) by(bit_vector)
        requires
            #(
                (N <= h) ==> spec_has_bit_set(val, N),
                (N > h) ==> !spec_has_bit_set(val, N),
            )*
            true;
    }
    }
});

verus! {
    pub open spec fn is_highest_bit(input: u64, bit: u64) -> bool {
        is_upper_bound_satisfy_cond(has_bit_closure(input), bit, 63)
    }

    #[verifier(inline)]
    pub open spec fn spec_fill_ones_exe(input: u64) -> u64 {
        let ret = input;
        let ret = ret | (ret >> 1);
        let ret = ret | (ret >> 2);
        let ret = ret | (ret >> 4);
        let ret = ret | (ret >> 8);
        let ret = ret | (ret >> 16);
        let ret = ret | (ret >> 32);
        ret
    }

    #[verifier(inline)]
    pub open spec fn spec_prev_power_of_two_exe(input: u64) -> u64 {
        if input == 0 {
            0
        } else {
            let ret = spec_fill_ones_exe(input);
            add((ret >> 1), 1)
        }
    }

    #[verifier(inline)]
    pub open spec fn spec_next_power_of_two_exe(input: u64) -> u64 {
        if input <= 1 {
            1
        } else {
            let ret = spec_fill_ones_exe(sub(input,1));
            add(ret, 1)
        }
    }

    #[verifier(inline)]
    pub open spec fn spec_highest_bit(input: u64) -> u64
    recommends
        input != 0,
    {
        choose |b: u64| is_highest_bit(input, b)
    }

    pub proof fn proof_get_highest_bit(input: u64) -> (ret: u64)
    requires
        input != 0,
    ensures
        is_highest_bit(input, ret),
        ret == spec_highest_bit(input),
        0 <= ret < 64,
    {
        let high_bit = choose |b: u64| is_highest_bit(input, b);
        let cond_fn = has_bit_closure(input);
        let exist_high_bit = exists |b: u64| is_highest_bit(input, b);
        let exist_has_bit = exists |b: u64| #[trigger]cond_fn(b) && b <= 63 ;
        if  !exist_high_bit {
            assert forall |b: u64| !#[trigger]is_upper_bound_satisfy_cond(cond_fn, b, 63) by{
                assert(!is_highest_bit(input, b));
                assert(is_highest_bit(input, b) === is_upper_bound_satisfy_cond(cond_fn, b, 63));
                assert(!is_upper_bound_satisfy_cond(cond_fn, b, 63));
            }
            assert(!exists |b: u64| is_upper_bound_satisfy_cond(cond_fn, b, 63));
            proof_has_conditional_upper_bound(cond_fn, 63);
            assert(!exist_has_bit);
            assert forall |b: u64| 0 <= b < 64
            implies !spec_has_bit_set(input, b)
            by{
                assert(!cond_fn(b));
            }
            lemma_zeroval_bits(input);
        }
        assert(exist_high_bit);
        assert(is_highest_bit(input, high_bit));
        high_bit
    }

    pub closed spec fn spec_prev_power_of_two(input: u64) -> u64 {
        if input != 0 {
            let high_bit = spec_highest_bit(input);
            BIT64!(high_bit)
        } else {
            0
        }
    }

    pub closed spec fn spec_next_power_of_two(input: u64) -> u64 {
        if input != 0 {
            let high_bit = spec_highest_bit(input);
            if input != BIT64!(high_bit) {
                BIT64!(add(high_bit, 1))
            } else {
                input
            }
        } else {
            1
        }
    }

    pub open spec fn spec_is_prev_power_of_two(input: nat, ret: nat) -> bool {
        &&& (input != 0) ==> (
            input/2nat < ret <= input &&
            spec_bit64_is_shl_by_bits(ret as u64)
        )
    }

    pub open spec fn spec_is_next_power_of_two(input: nat, ret: nat) -> bool {
        &&& spec_bit64_is_shl_by_bits(ret as u64)
        &&& ret == spec_next_power_of_two_exe(input as u64)
        &&& (input != 0) ==> input <= ret < input * 2
    }

    pub proof fn lemma_fill_ones(input: u64) -> (ret: u64)
    requires
        input != 0,
    ensures
        ret == spec_fill_ones_exe(input),
        (ret >> 1) < u64::MAX,
        (!ret & input) == 0,
        (ret & input) == input,
        ret / 2 < input,
        ret >= input,
        ret == nbits_mask(add(spec_highest_bit(input),1)),
    {
        let ret = spec_fill_ones_exe(input);
        assert((!ret & input) == 0 && ((ret & input) == input)) by(bit_vector)
        requires
            ret == spec_fill_ones_exe(input);
        let high_bit = proof_get_highest_bit(input);
        assert(1 == BIT64!(0u64)) by(bit_vector);
        assert(has_bits_until(input, 1, high_bit)) by {
            assert forall |b: u64| (high_bit < b < 64)
            implies !spec_has_bit_set(input, b)
            by {
                assert(is_highest_bit(input, high_bit));
                if spec_has_bit_set(input, b) {
                    assert(has_bit_closure(input)(b) && b <= 63);
                    assert(b <= high_bit);
                }
            }
        }
        lemma_fill_ones_bit_steps(input, 1, high_bit, 0);
        bit64_shl_auto();

        assert(ret == fill_ones(input)) by {
            reveal_with_fuel(_fill_ones, 7);
        }
        assert(ret == nbits_mask(add(high_bit,1)));
        assert((ret >> 1) < u64::MAX) by(bit_vector);
        assert(ret >= 1) by(bit_vector)
        requires
            0 <= high_bit < 64,
            ret == nbits_mask(add(high_bit,1));
        assert((!ret & input) == 0 && (ret / 2 < input) && (ret >= input)) by(bit_vector)
        requires
            input != 0,
            ret == spec_fill_ones_exe(input);
        assert((ret & input) == input) by(bit_vector)
        requires
            input != 0,
            ret == spec_fill_ones_exe(input);
        ret
    }

    pub proof fn lemma_prev_power_of_two(input: u64) -> (ret: u64)
    ensures
        spec_is_prev_power_of_two(input as nat, ret as nat),
        ret == spec_prev_power_of_two_exe(input),
    {
        if input == 0 {
            assert(spec_is_prev_power_of_two(0, 0));
            0
        } else {
            let ret = lemma_fill_ones(input);
            let ret_last = add((ret >> 1u64), 1u64);
            let high_bit = proof_get_highest_bit(input);
            assert(add((ret >> 1u64), 1u64) == BIT64!(high_bit)) by(bit_vector)
            requires
                ret == nbits_mask(add(high_bit, 1)),
                0 <= high_bit < 64;
            assert(spec_bit64_is_shl_by_bits(ret_last)) by(bit_vector)
            requires
                ret == nbits_mask(add(high_bit, 1)),
                ret_last == add((ret >> 1u64), 1u64),
                0 <= high_bit < 64;
            assert(input >> 1 == input / 2) by(bit_vector);
            assert((input >> 1) < ret_last <= input) by(bit_vector)
            requires
                input != 0,
                ret_last == spec_prev_power_of_two_exe(input);
            ret_last
        }
    }

    pub proof fn lemma_next_power_of_two(input: u64) -> (ret: u64)
    requires
        input <= POW2!(63),
    ensures
        spec_bit64_is_shl_by_bits(ret as u64),
        spec_is_next_power_of_two(input as nat, ret as nat),
        ret == spec_next_power_of_two_exe(input),
        input > 1 ==> spec_fill_ones_exe(sub(input, 1)) < u64::MAX,
    {
        if input <= 1 {
            bit_shl64_pow2_auto();
            assert(spec_bit64_is_shl_by_bits(1));
            1
        } else {
            let input1 = sub(input, 1);
            let fill_ones = lemma_fill_ones(input1);
            let high_bit = proof_get_highest_bit(input1);
            let ret = add(fill_ones, 1);
            assert(fill_ones < u64::MAX) by(bit_vector)
            requires
                0 < input1 < POW2!(63),
                fill_ones/2 < input1;
            assert(spec_bit64_is_shl_by_bits(ret)) by(bit_vector)
            requires
                fill_ones == nbits_mask(add(high_bit, 1)),
                ret == add(fill_ones, 1u64),
                fill_ones < u64::MAX,
                0 <= high_bit < 64;
            ret
        }
    }

    spec fn _fill_ones(input: u64, nbits: u64, round: u64) -> u64
    recommends
        round <= 6,
        nbits == BIT64!(round),
    decreases
        6 - round,
    {
        if round < 6 {
            let t = input | (input >> nbits);
            _fill_ones(t, BIT64!(add(round, 1)), add(round, 1))
        } else {
            input
        }
    }

    spec fn fill_ones(input: u64) -> u64 {
        _fill_ones(input, 1, 0)
    }

    proof fn lemma_fill_ones_bit_step(input: u64, nbits: u64, h: u64, round: u64) -> (ret: (u64, u64))
    requires
        nbits == BIT64!(round),
        round < 6,
        h < 64,
        has_bits_until(input, nbits, h),
    ensures
        ret.0 == (input | input >> nbits),
        ret.1 == BIT64!(add(round, 1)),
        has_bits_until(ret.0, ret.1, h),
    {
        assert(0 < nbits < 64) by {
            bit64_shl_auto();
            assert(BIT64!(round) < BIT64!(6u64)) by(bit_vector)
            requires round < 6;
        }
        let nbits2: u64 = BIT64!(add(round, 1));
        assert(nbits2 == add(nbits, nbits)) by(bit_vector)
        requires
            nbits == BIT64!(round),
            nbits2 == BIT64!(add(round, 1)),
            round < 6
        ;
        assert(BIT64!(round) <= 32) by(bit_vector)
        requires round < 6;
        let ret = (input | input >> nbits);
        assert forall |b: u64|
            b <= h  && sub(h, b) < nbits2
        implies
            spec_has_bit_set(ret, b)
        by {
            bit64_or_auto();
            if b <= h  && sub(h, b) < nbits {
                assert(spec_has_bit_set(input, b));
                assert(spec_has_bit_set(ret, b));
            } else {
                assert(spec_has_bit_set(input >> nbits, b)) by(bit_vector)
                requires
                    0 < h < 64,
                    0 < nbits < 64,
                    spec_has_bit_set(input, add(b, nbits)),
                    b <= h,
                    sub(h, add(b, nbits)) < nbits;
                assert(spec_has_bit_set(ret, b));
            }
        }
        assert forall |b: u64|
            h < b < 64
        implies
            !spec_has_bit_set(ret, b)
        by {
            assert(!spec_has_bit_set(input, b));
            assert(!spec_has_bit_set(input >> nbits, b)) by{
                if add(b, nbits) < 64 {
                    assert(!spec_has_bit_set(input >> nbits, b)) by(bit_vector)
                    requires
                        b < 64,
                        nbits < 64,
                        add(b, nbits) < 64,
                        !spec_has_bit_set(input, add(b, nbits)),
                } else {
                    assert(!spec_has_bit_set(input >> nbits, b)) by(bit_vector)
                    requires
                        b < 64,
                        nbits < 64,
                        add(b, nbits) >= 64;
                }
            }
            assert(!spec_has_bit_set(input | (input >> nbits), b)) by(bit_vector)
            requires
                0 < nbits < 64,
                h < b < 64,
                !spec_has_bit_set(input, b),
                !spec_has_bit_set(input >> nbits, b);
        }
        (ret, nbits2)
    }

    proof fn lemma_fill_ones_bit_steps(input: u64, nbits: u64, h: u64, round: u64) -> (ret: u64)
    requires
        round <= 6,
        h < 64,
        has_bits_until(input, nbits, h),
        nbits == BIT64!(round),
    ensures
        ret == _fill_ones(input, nbits, round),
        has_bits_until(ret, 64, h),
        ret == nbits_mask(add(h,1)),
    decreases
        6 - round,
    {
        let ret = _fill_ones(input, nbits, round);
        if round < 6 {
            let (t, nbits2) = lemma_fill_ones_bit_step(input, nbits, h, round);
            lemma_fill_ones_bit_steps(t, nbits2, h, add(round, 1));
            assert(has_bits_until(_fill_ones(t, nbits2, add(round, 1)), 64, h));
            assert(ret == _fill_ones(t, nbits2, add(round, 1)));
            assert(has_bits_until(ret, 64, h));
        } else {
            assert(BIT64!(round) == 64) by(bit_vector)
            requires round == 6;
            assert(has_bits_until(input, 64, h));
            assert(ret == input);
        }
        lemma_has_64bits_until_to_mask(ret, h);
        ret
    }


}

/*
macro_rules! define_integer_ex_fn {
    ($T: ty, $N: expr) => {
        paste::paste! {
    verus!{
    pub open spec fn [<spec_is_leading_zeros_ $T>](val: $T, ret: u32) -> bool {
        let mask: $T = (1 as $T) << ($N - ret - 1) as $T;
        &&& ret as int == spec_leading_zeros(val)
        &&& if ret == $N {
            val == 0
        } else if ret == 0 {
            val & mask == mask
        } else {
            let base: $T = (((1 as $T) << ($N - ret) as $T) as $T- 1 as $T) as $T;
            let leading: $T = !base;
            &&& ret <= $N
            &&& val & leading == 0
            &&& val & mask == mask
        }
    }
    #[verifier::external_fn_specification]
    pub fn [<ex_leading_zeros_ $T>](val: $T) -> (ret: u32)
        ensures [<spec_is_leading_zeros_ $T>](val, ret)
    {
        val.leading_zeros()
    }
    }
    }
}
}

define_integer_ex_fn!(u64, 8);
define_integer_ex_fn!(u32, 4);
define_integer_ex_fn!(u16, 2);
*/
