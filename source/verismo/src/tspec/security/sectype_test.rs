//impl_secure_type!{(), type}
use core::ops::*;

use super::*;

impl_secure_type! {(), type}
use vops::VEq;

verus! {
// Surface the SecType constructor/extensionality axioms for every proof in
// this test module.  Without this, postconditions involving `spec_new(...)`
// (e.g. `v1 + v2`, `v1 * v2`, casts) are opaque to the verifier.
broadcast use SecType::axiom_spec_new, SecType::axiom_ext_equal;
}

mod p {
    use super::*;
    verus! {

// assert by cannot exist with broadcast forall with trait bound.
pub proof fn proof_test1(v1: u64, v2: u64)
    requires
        v1 < 10,
        v2 < 10,
    ensures
        v1 * v2 < 100,
{
    assert(v1 * v2 < 100) by (nonlinear_arith)
        requires
            v1 < 10,
            v2 < 10,
    ;
}

pub proof fn proof_test_bits2(v1: u64, v2: u64)
    requires
        v1 < 10,
        v2 < 10,
    ensures
        v1 & v2 < 10,
{
    assert(v1 & v2 < 10) by (bit_vector)
        requires
            v1 < 10,
            v2 < 10,
    ;
}

} // verus!
}

verismo! {
    fn test_add (v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1@.val + v2@.val <= u64::MAX,
    {
        proof {
            use_type_invariant(&v1);
            use_type_invariant(&v2);
        }
        v1.add(v2)
    }

    fn test1(v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1@.val < 10,
        v2@.val < 10,
    ensures
        v1 * v2 < 100,
    {
        proof {
            use_type_invariant(&v1);
            use_type_invariant(&v2);
        }
        v1.add(v2)
    }

    fn test2 (v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1@.val * v2@.val <= u64::MAX,
    {
        let v = 11;
        assert(v1@.val >= 0);
        assert(v2@.val >= 0);
        assert(v1@.val >= 0) by {
            assert(v1@.val >= 0)
        }
        v
    }
}

verismo! {
    proof fn proof_u64_s(v1: u64_s, v2: u64_s)
    requires
        v1 > v2,
        v1 + v2 <= u64::MAX,
    ensures
        (v1 + v2)@.val == (v1@.val + v2@.val),
        (v1 + v2)@.valsets[1] =~~= set_op(v1@.valsets[1], v2@.valsets[1], |v1: u64, v2: u64| (v1 + v2)),
    {
    }

    /*proof fn test_bit(v1: u64_s, v2: u64_s)
    requires
        v2 == 11,
    ensures
        v1 >> v2 == v1 / (1u64_s << v2)
    {
        assert(v2 < 64);
        // bit-vector does not support call fn
        //assert(v1 << v2 == v1 / (1u64_s << v2)) by(bit_vector)
        //requires v2@.val < 64u64;

        assert(v1 >> v2 == v1 / (1u64_s << v2)) by {
            let val1: u64 = v1@.val;
            let val2: u64 = v2@.val;
            /*assert((v1 >> v2)@.val == val1 >> val2);
            assert(1u64_s@.val == 1u64);
            assert( (1u64_s << v2)@.val === (1u64 << val2));*/
            assert((v1 / (1u64_s << v2))@.val == val1 / (1u64 << val2));
            assert(val1 >> val2 == val1 / (1u64 << val2)) by(bit_vector)
            requires val2 == 11u64;
        }
    }*/
}

verismo_non_secret! {
    fn test_bits2(v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1 < 10,
        v2 < 10,
    ensures
        v1 & v2 < 10,
    {
        proof {p::proof_test_bits2(v1 as u64, v2 as u64)}

        if v1 & v2 == 4 {
            proof {
                assert(v1 & v2 == 4);
            }
        }

        if v1 & v2 != 4 {
            proof {
                assert(v1 & v2 != 4);
            }
        }
        v1 & v2
    }
}

verismo! {
    fn test_not(v1: u64_s) -> (ret: u64_s)
    requires
        v1 == 10,
    ensures
        ret@.val == !((v1@.val - 1) as u64),
    {
        proof {
            use_type_invariant(&v1);
        }
        let mask = v1 - 1;
        proof {
            use_type_invariant(&mask);
        }
        let ret = (!mask);
        ret
    }

    fn test_add2(v1: u64) -> (ret: u64)
    requires
        v1 == 0xff
    ensures
        ret == 0x100
    {
        proof {
            use_type_invariant(&v1);
        }
        v1 + 1
    }

    fn test_cast(v1: u64) -> (ret: u32)
    requires
        v1 == 0xff,
    ensures
        ret == 0xff,
        v1@.val == 0xff,
        ret@.val == 0xff,
    {
        proof {
            use_type_invariant(&v1);
        }
        v1 as u32
    }
}
