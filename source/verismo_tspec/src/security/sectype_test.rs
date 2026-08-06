//impl_secure_type!{(), type}
use core::ops::*;

use super::*;

impl_secure_type! {(), type}
use vops::VEq;

verus! {

// Required in this in-crate test module; downstream default broadcasts do not surface these here.
broadcast use {
    SecType::axiom_spec_new,
    SecType::axiom_ext_equal,
    SpecSecType::axiom_uop_new_constant,
};

} // verus!
mod p {
    use super::*;
    #[rustfmt::skip]
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

// `verismo_simple!` (update_conditions = false) still rewrites secure types
// and operators, but never synthesizes a constantness contract: unlike
// `verismo!`/`verismo_non_secret!`, no implicit `is_constant()` requires or
// ensures are added, so any such fact must be requested explicitly, as done
// here.
verismo_simple! {
    fn test_simple_add(v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1.is_constant(),
        v2.is_constant(),
        v1@.val + v2@.val <= u64::MAX,
    ensures
        ret@.val == v1@.val + v2@.val,
        ret.is_constant(),
    {
        v1.add(v2)
    }
}

verismo! {
    fn test_add (v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1@.val + v2@.val <= u64::MAX,
    {
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
            // Bridge `(v1 * v2) < 100` to a nonlinear-arith fact on raw u64.
            // (v1*v2).ord_int() inlines to v1@.bop_new(v2@, fn_spec_mul_u64_u64_int).val
            // which equals v1@.val * v2@.val via fn_spec_mul's lambda body.
            let val1: u64 = v1@.val;
            let val2: u64 = v2@.val;
            assert(val1 * val2 < 100) by (nonlinear_arith)
                requires
                    val1 < 10,
                    val2 < 10,
            ;
        }
        v1.add(v2)
    }

    fn test2 (v1: u64_s, v2: u64_s) -> (ret: u64_s)
    requires
        v1@.val * v2@.val <= u64::MAX,
    {
        let v = 11;
        v
    }
}

verus! {

// `test_simple_add` (via `verismo_simple!`) never has an `is_constant()`
// contract synthesized for it, so its `ensures ret.is_constant()` above is
// stated explicitly by the function author. This client satisfies the
// explicit `is_constant()` preconditions with constant secure integers and
// relies solely on that explicitly stated postcondition (not any
// macro-synthesized fact) to establish the result is constant.
fn test_simple_add_caller() {
    let v1 = u64_s::constant(3);
    let v2 = u64_s::constant(4);
    let ret = test_simple_add(v1, v2);
    assert(ret.is_constant());
}

// `test_add` above has no explicit `is_constant()` contract, and its
// signature does not require constant inputs. Yet because it is defined
// inside `verismo!` (update_conditions = true, for_non_secret = false), the
// macro synthesizes an implicit `imply(inputs constant, output constant)`
// postcondition. This client calls `test_add` with constant secure integers
// and relies solely on that synthesized postcondition (no manual proof) to
// establish the result is constant.
fn test_add_constant_propagation() {
    let v1 = u64_s::constant(3);
    let v2 = u64_s::constant(4);
    let ret = test_add(v1, v2);
    assert(ret.is_constant());
}

// `verismo!` does not synthesize an `is_constant()` *precondition* for
// `test_add`: its only requirement is the arithmetic overflow bound copied
// from the function body. This client calls `test_add` with arbitrary
// (non-constant) secure integers, satisfying only that arithmetic
// precondition, to demonstrate the call type-checks and verifies without
// any constantness requirement on the inputs. It makes no claim about the
// constantness of the result.
fn test_add_non_constant(v1: u64_s, v2: u64_s)
    requires
        v1@.val + v2@.val <= u64::MAX,
{
    let _ret = test_add(v1, v2);
}

} // verus!
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
        // Required to prove the bit-vector bound from the non-secret operands.
        proof {p::proof_test_bits2(v1 as u64, v2 as u64)}

        v1 & v2
    }
}

verismo! {
    fn test_not(v1: u64_s) -> (ret: u64_s)
    requires
        v1 == 10,
    ensures
        ret@.val == !((v1@.val - 1) as u64),
        ret.wf_value(),
    {
        let mask = v1 - 1;
        !mask
    }

    fn test_add2(v1: u64) -> (ret: u64)
    requires
        v1 == 0xff
    ensures
        ret == 0x100
    {
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
        v1 as u32
    }
}
