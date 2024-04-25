#[allow(unused_imports)]
use super::*;

#[macro_export]
macro_rules! BIT {
    ($x: expr) => {
        (1 << ($x))
    };
}

#[macro_export]
macro_rules! BIT64 {
    ($x: expr) => {
        (1u64 << (($x) as u64))
    };
}

verus! {
#[verifier(inline)]
pub open spec fn spec_bit64(val: u64) -> u64 {
    1u64 << val
}
}

#[macro_export]
macro_rules! POW2 {
    (0) => {
        0x1u64
    };
    (1) => {
        0x2u64
    };
    (2) => {
        0x4u64
    };
    (3) => {
        0x8u64
    };
    (4) => {
        0x10u64
    };
    (5) => {
        0x20u64
    };
    (6) => {
        0x40u64
    };
    (7) => {
        0x80u64
    };
    (8) => {
        0x100u64
    };
    (9) => {
        0x200u64
    };
    (10) => {
        0x400u64
    };
    (11) => {
        0x800u64
    };
    (12) => {
        0x1000u64
    };
    (13) => {
        0x2000u64
    };
    (14) => {
        0x4000u64
    };
    (15) => {
        0x8000u64
    };
    (16) => {
        0x10000u64
    };
    (17) => {
        0x20000u64
    };
    (18) => {
        0x40000u64
    };
    (19) => {
        0x80000u64
    };
    (20) => {
        0x100000u64
    };
    (21) => {
        0x200000u64
    };
    (22) => {
        0x400000u64
    };
    (23) => {
        0x800000u64
    };
    (24) => {
        0x1000000u64
    };
    (25) => {
        0x2000000u64
    };
    (26) => {
        0x4000000u64
    };
    (27) => {
        0x8000000u64
    };
    (28) => {
        0x10000000u64
    };
    (29) => {
        0x20000000u64
    };
    (30) => {
        0x40000000u64
    };
    (31) => {
        0x80000000u64
    };
    (32) => {
        0x100000000u64
    };
    (33) => {
        0x200000000u64
    };
    (34) => {
        0x400000000u64
    };
    (35) => {
        0x800000000u64
    };
    (36) => {
        0x1000000000u64
    };
    (37) => {
        0x2000000000u64
    };
    (38) => {
        0x4000000000u64
    };
    (39) => {
        0x8000000000u64
    };
    (40) => {
        0x10000000000u64
    };
    (41) => {
        0x20000000000u64
    };
    (42) => {
        0x40000000000u64
    };
    (43) => {
        0x80000000000u64
    };
    (44) => {
        0x100000000000u64
    };
    (45) => {
        0x200000000000u64
    };
    (46) => {
        0x400000000000u64
    };
    (47) => {
        0x800000000000u64
    };
    (48) => {
        0x1000000000000u64
    };
    (49) => {
        0x2000000000000u64
    };
    (50) => {
        0x4000000000000u64
    };
    (51) => {
        0x8000000000000u64
    };
    (52) => {
        0x10000000000000u64
    };
    (53) => {
        0x20000000000000u64
    };
    (54) => {
        0x40000000000000u64
    };
    (55) => {
        0x80000000000000u64
    };
    (56) => {
        0x100000000000000u64
    };
    (57) => {
        0x200000000000000u64
    };
    (58) => {
        0x400000000000000u64
    };
    (59) => {
        0x800000000000000u64
    };
    (60) => {
        0x1000000000000000u64
    };
    (61) => {
        0x2000000000000000u64
    };
    (62) => {
        0x4000000000000000u64
    };
    (63) => {
        0x8000000000000000u64
    };
    ($_:expr) => {
        0u64
    };
}

#[macro_export]
macro_rules! BIT32 {
    ($x: expr) => {
        (1u32 << ($x))
    };
}

#[macro_export]
macro_rules! BIT16 {
    ($x: expr) => {
        (1u16 << ($x))
    };
}

#[macro_export]
macro_rules! BIT8 {
    ($x: expr) => {
        (1u8 << ($x))
    };
}

#[macro_export]
macro_rules! BIT_MASK {
    ($x: expr) => {
        sub((1u64 << ($x)), 1)
    };
}

verus! {
#[verifier(inline)]
pub open spec fn spec_bit_set(val: u64, bit: u64) -> u64 {
    val | BIT64!(bit)
}

#[verifier(inline)]
pub open spec fn spec_bit_clear(val: u64, bit: u64) -> u64 {
    val & (!BIT64!(bit))
}

#[verifier(inline)]
pub open spec fn spec_has_bit_set(val: u64, bit: u64) -> bool {
    #[trigger] BIT64!(bit) == val & BIT64!(bit)
    //&&& 0 <= bit < 64
}

#[verifier(bit_vector)]
pub proof fn proof_bit_check(val: u64, bit: u64)
requires
    bit < 64,
ensures
    spec_has_bit_set(spec_bit_set(val, bit), bit),
    !spec_has_bit_set(spec_bit_clear(val, bit), bit),
{}
}

macro_rules! mask_proof_for_bits_internal {
    [$($N:expr),* $(,)?] => {
        verus!{
        pub open spec fn slow_bit_range_req(bits: u64) -> bool {
            $(
                ||| (bits == $N)
            )*
        }
        pub proof fn slow_bit_mask64_mod_auto(bits: u64)
            requires
                slow_bit_range_req(bits)
            ensures
                forall |a: u64| #![auto] (a & BIT_MASK!(bits)) == a % BIT64!(bits),
                forall |a: u64| #![auto] (a|BIT_MASK!(bits)) == add(sub(a, (a&BIT_MASK!(bits))), BIT_MASK!(bits)),
                forall |a: u64| #![auto] add(a & !(BIT_MASK!(bits)), BIT_MASK!(bits)) >= a,
        {
            bit_shl64_auto();
            bit_and64_auto();
            bit_or64_auto();
            $(
            assert(forall |a: u64| #![auto] (a & BIT_MASK!($N)) == a % BIT64!($N)) by(bit_vector);
            assert(forall |a: u64| #![auto] (a|BIT_MASK!($N)) == add(sub(a, (a&BIT_MASK!($N))), BIT_MASK!($N))) by(bit_vector);
            assert(forall |a: u64| #![auto]  add(a & !(BIT_MASK!($N)), BIT_MASK!($N)) >= a) by(bit_vector);
            )*
        }
    }
    };
}

macro_rules! mask_proof_for_bits {
    [$($tail:tt)*] => {
        mask_proof_for_bits_internal!($($tail)*);
    };
}

seq_macro::seq!(N in 0..64 {
verus!{
#[verifier(bit_vector)]
pub proof fn bit_shl64_auto()
    ensures
        forall |a: u64| #[trigger] (a<<0u64) == a,
        forall |a: u64| a < 64 ==> #[trigger] (1u64<<a) > 0,
        forall |a: u64, b: u64| b < 64 ==> ((a & BIT64!(b) ==  BIT64!(b)) || (a & BIT64!(b) == 0)),
        #(
        BIT64!(N as u64) == POW2!(N),
        )*
{}

pub proof fn bit_shl64_pow2_auto()
    ensures
        #(
        BIT64!(N as u64) == POW2!(N),
        )*
{
    bit_shl64_auto()
}
}
}
);

verus! {
    // Add more when necessary; We may add all between [0,64)
    mask_proof_for_bits!(
        2u64,
        3u64,
        12u64,
    );

    #[verifier(bit_vector)]
    pub const proof fn bit_and64_auto()
        ensures
            forall |a: u64, b: u64| #[trigger] (a&b) == b&a ,
            forall |a: u64, b: u64, c:u64| #[trigger] ((a&b)&c) == a&(b&c),
            forall |a: u64| #[trigger] (a&a) == a,
            forall |a: u64| #[trigger] (a&0) == 0,
            forall |a: u64| #[trigger] (a& 0xffffffffffffffffu64) == a,
            forall |a: u64, b: u64| #[trigger] (a&b) <= b,
            forall |a: u32, b: u32| #[trigger] (a&b) <= b,
            forall |a: u16, b: u16| #[trigger] (a&b) <= b,
            forall |a: u8, b: u8| #[trigger] (a&b) <= b,
    {}


    /*
    #[verifier(bit_vector)]
    pub proof fn bit64_and_mask_mask_auto()
        ensures
            forall |a: u64, bits: u64| #![auto] 0<= bits < 64 ==> (a & BIT_MASK!(bits)) == a % BIT64!(bits)
    {}
    */

    #[verifier(bit_vector)]
    pub proof fn bit64_or_mask_auto()
        ensures
            forall |a: u64, bits: u64| #![auto] 0<= bits < 64 ==> (add(a|BIT_MASK!(bits), 1)) & BIT_MASK!(bits) == 0,
    {}

    #[verifier(bit_vector)]
    pub proof fn bit_or64_auto()
        ensures
            forall |a: u64, b: u64, c: u64| (a & c == c) ==> ((a | b) & c == c),
            forall |a: u64, b: u64| #[trigger] (a|b) == b|a,
            forall |a: u64, b: u64, c:u64| #[trigger] ((a|b)|c) == a|(b|c),
            forall |a: u64| #[trigger] (a|a) == a,
            forall |a: u64| #[trigger] (a|0) == a,
            forall |a: u64| #[trigger] (a| 0xffffffffffffffffu64) == 0xffffffffffffffffu64,
            forall |a: u64, b: u64| #[trigger] (a|b) <= 0xffffffffffffffffu64,
            //forall |a: u64, b: u64| #[trigger] (a|b) <= add(sub(a, a&b), b),
            forall |a: u64, b: u64| #[trigger] (a|b) >= a,
    {}

    /*
    //Resource limit (rlimit) exceeded
    pub proof fn bit_or64_rel_add_auto()
    ensures
        forall |a: u64, b: u64| a < sub(0xffffffffffffffffu64, b) ==> #[trigger] (a|b) <= add(a, b),
    {
        assert forall |a: u64, b: u64|
        #[trigger] (a|b) <= add(a, b)
        by {
            assert((a|b) <= add(a, b)) by(bit_vector)
        }
    }*/

    #[verifier(bit_vector)]
    pub proof fn bit_xor64_auto()
        ensures
            forall |a: u64, b: u64| #[trigger] (a^b) == b^a,
            forall |a: u64, b: u64, c:u64| #[trigger] ((a^b)^c) == a^(b^c),
            forall |a: u64| #[trigger] (a^a) == 0,
            forall |a: u64| #[trigger] (a^0) == a,
            forall |a: u64| #[trigger] (a^ 0xffffffffffffffffu64) == !a,
    {}

    #[verifier(bit_vector)]
    pub proof fn bit_not64_auto()
        ensures
            forall |a: u64| #[trigger] !(!a) == a,
            forall |a: u64| #[trigger] (!a) & a == 0,
            !0u64 == 0xffffffffffffffffu64,
            forall |a: u64| #[trigger] (!a) == sub(MAXU64!(), a),
    {}

    #[verifier(bit_vector)]
    pub proof fn proof_bit_u64_not(a: u64)
    ensures
        (!a) == sub(MAXU64!(), a)
    {}

    #[verifier(bit_vector)]
    pub proof fn proof_bit_usize_not(a: usize)
    ensures
        (!a) == sub(MAXU64!() as usize, a)
    {}

    #[verifier(bit_vector)]
    pub proof fn bit_lsh64_auto()
        ensures
            forall |a: u64| #[trigger] (a>>0u64) == a,
    {}

    #[verifier(bit_vector)]
    pub proof fn bit_property64_auto()
        ensures
            // absorb
            forall |a: u64, b: u64| #[trigger] (a & (a | b)) == a,
            forall |a: u64, b: u64| #[trigger] (a | (a & b)) == a,
            forall |a: u64, b: u64| #[trigger] (a & ((!a) & b)) == 0,
            forall |a: u64, b: u64|  a == 0 || #[trigger] ((!a) & b) != #[trigger] (a | b),
            // distributive
            forall |a: u64, b: u64, c:u64| #[trigger] (a & (b | c)) == (a & b) | (a & c),
            forall |a: u64, b: u64, c:u64| #[trigger] (a & (b ^ c)) == (a & b) ^ (a & c),
            forall |a: u64, b: u64, c:u64| #[trigger] (a | (b & c)) == (a | b) & (a | c),
            // De Morgan
            forall |a: u64, b: u64| #[trigger] (!(a & b)) == !a | !b,
            forall |a: u64, b: u64| #[trigger] (!(a | b)) == !a & !b,
    {
    }

    pub proof fn bit_set_non_zero(val: u64, b: u64)
    requires
        0 <= b < 64,
    ensures
        bits_p::spec_bit_set(val, b) > 0
    {
        assert(bits_p::spec_bit_set(val, b) > 0) by (bit_vector)
        requires
            0 <= b < 64;
    }
}

seq_macro::seq!(N in 0..64 {
verus!{
    pub proof fn bit_rsh64_div_rel(b: u64, a: u64) -> (ret: u64)
    requires
        a < 64,
    ensures
        ret == (b >> a),
        ret * BIT64!(a) <= MAXU64!(),
        (b>>a) == (b / BIT64!(a)),
    {
        let ret = (b >> a);
        #(
            if a == N {
                assert(ret == b / BIT64!(N as u64)) by(bit_vector)
                requires ret == (b >> N);
                assert(b <= MAXU64!());
                bit_shl64_pow2_auto();
                assert(b / POW2!(N) * POW2!(N) <= MAXU64!());
            }
        )*
        ret
    }
}
});

seq_macro::seq!(N in 0..64 {
    verus!{
        pub proof fn bit_lsh64_mul_rel(b: u64, a: u64)
        requires
            a < 64,
            b * BIT64!(a) <= MAXU64!(),
        ensures
            (b<<a) == (b * BIT64!(a)),
        {
            #(
                 if a == N {
                    assert((b<<N) == mul(b, BIT64!(N as u64))) by(bit_vector);
                    bit_shl64_pow2_auto();
                    assert(b * BIT64!(N as u64) <= MAXU64!());
                    assert(mul(b, POW2!(N)) == b * POW2!(N));
                    assert((b<<N) == b * BIT64!(N));
                }
            )*
            assert((b<<a) == b * BIT64!(a));

        }
    }
});

seq_macro::seq!(N in 0..64 {
verus!{
    pub proof fn proof_bit_u64_and_rel_mod(a: u64, b: u64)
    requires
        spec_bit64_is_pow_of_2(b as int),
    ensures
        a & sub(b, 1) == a % b
    {
        #(
            assert(a & sub(POW2!(N), 1) == a % POW2!(N)) by(bit_vector);
        )*
    }

    pub proof fn proof_bit_usize_and_rel_mod(a: usize, b: usize)
    requires
        spec_bit64_is_pow_of_2(b as int),
    ensures
        a & sub(b, 1) == a % b
    {
        #(
            assert(a & sub(POW2!(N) as usize, 1) == a % (POW2!(N)  as usize)) by(bit_vector);
        )*
    }
}
}
);

#[macro_export]
macro_rules! lemma_bits64 {
    () => {
        bit_property64_auto();
        bit_and64_auto();
        bit_or64_auto();
        bit_xor64_auto();
        bit_not64_auto();
        bit_lsh64_auto();
        bit_shl64_auto();
    };
}
