use super::*;

verus! {

#[verifier(nonlinear)]
pub proof fn proof_mod_mod(a: int, b: int)
    requires
        b > 0,
    ensures
        a % b % b == a % b,
{
}

#[verifier(nonlinear)]
pub proof fn lemma_mod(a: int, b: int) -> (ret: int)
    requires
        b > 0,
        a % b == 0,
    ensures
        ret * b == a,
{
    a / b
}

// Z3 is too slow with this proof
//#[verifier(nonlinear)]
#[verifier(external_body)]
pub proof fn lemma_mod_from_mul_rel(a: int, b: int, c: int)
    requires
        b != 0,
        a == b * c,
    ensures
        a % b == 0,
{
}

pub proof fn proof_mod_propogate(a: int, b: int, c: int)
    requires
        b > 0,
        c > 0,
        a % b == 0,
        b % c == 0,
    ensures
        a % c == 0,
{
    let d1 = lemma_mod(a, b);
    let d2 = lemma_mod(b, c);
    assert((d1 * d2) * c == a) by {
        assert(a == d1 * (d2 * c));
        proof_mul_dist(d1, d2, c);
    }
    let d = d1 * d2;
    assert(d * c == a);
    proof_mul_exchange(d, c);
    lemma_mod_from_mul_rel(a, c, d);
}

#[verifier(nonlinear)]
pub proof fn proof_mul_assoc(a: nat, b: nat, c: nat)
    ensures
        (a + b) * c == a * c + b * c,
{
}

#[verifier(nonlinear)]
pub proof fn proof_mul_bound(a: u64, b: u64, aa: int, bb: int)
    requires
        a as int == aa,
        b as int == bb,
        aa > 0,
        bb > 0,
        a * b <= 0xffff_ffff_ffff_ffffu64,
    ensures
        aa * bb == mul(a, b),
        aa * bb > 0,
{
}

#[verifier(nonlinear)]
pub proof fn proof_div_mod_rel(a: int, b: int) -> (ret: int)
    requires
        b != 0,
    ensures
        ret == a / b,
        ret * b + (a % b) == a,
{
    a / b
}

#[verifier(nonlinear)]
pub proof fn proof_mul_dist(a: int, b: int, c: int) -> (ret: int)
    ensures
        ret == a * b * c,
        a * b * c == a * (b * c),
{
    a * b * c
}

#[verifier(nonlinear)]
pub proof fn proof_mul_div_rel(a: int, b: int) -> (ret: int)
    requires
        b != 0,
    ensures
        ret == a * b,
        ret / b == a,
{
    a * b
}

#[verifier(nonlinear)]
pub proof fn proof_mul_exchange(a: int, b: int) -> (ret: int)
    ensures
        ret == a * b,
        ret == b * a,
{
    a * b
}

pub proof fn proof_mod_range(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        0 <= a % b < b,
{
}

#[verifier(nonlinear)]
pub proof fn proof_mod_pos_neg_rel(a: int, b: int) -> (ret: int)
    requires
        b != 0,
    ensures
        ret == a % b,
        (b > 0) ==> 0 <= ret < b,
        (b < 0) ==> 0 <= ret < -b,
{
    a % b
}

#[verifier(nonlinear)]
pub proof fn proof_mul_pos_neg_rel(a: int, b: int) -> (ret: int)
    ensures
        ret == a * b,
        ((a > 0 && b > 0) || (a < 0 && b < 0)) ==> ret > 0,
        ((a > 0 && b < 0) || (a < 0 && b > 0)) ==> ret < 0,
        (a == 0 || b == 0) ==> ret == 0,
{
    a * b
}

#[verifier(inline)]
pub open spec fn abs(a: int) -> int {
    if a > 0 {
        a
    } else {
        -a
    }
}

#[verifier(nonlinear)]
pub proof fn proof_div_pos_neg_rel(a: int, b: int) -> (ret: int)
    requires
        b != 0,
    ensures
        ret == a / b,
        (a / b > 0) ==> ((a >= b && b > 0) || (a < 0 && b < 0)),
        ((a >= b && b > 0) || (a < b && b < 0)) ==> (a / b > 0),
        (a / b == 0) == (0 <= a < abs(b)),
{
    a / b
}

} // verus!
