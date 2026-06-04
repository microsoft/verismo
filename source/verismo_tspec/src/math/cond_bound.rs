use super::*;

verus! {

pub trait U64Predicate {
    spec fn call(&self, x: u64) -> bool;
}

pub open spec fn is_upper_bound_satisfy_cond<P: U64Predicate>(
    cond: &P,
    bound: u64,
    max: u64,
) -> bool {
    &&& cond.call(bound)
    &&& bound <= max
    &&& forall|b: u64| (#[trigger] cond.call(b) && b <= max) ==> b <= bound
}

proof fn lemma_has_conditional_upper_bound<P: U64Predicate>(val: u64, cond: &P, max: u64)
    requires
        cond.call(val),
        val <= max,
    ensures
        exists|val| #[trigger] is_upper_bound_satisfy_cond(cond, val, max),
    decreases max - val,
{
    let exist_bound = exists|val| #[trigger] is_upper_bound_satisfy_cond(cond, val, max);
    if !exist_bound {
        assert forall|val| !is_upper_bound_satisfy_cond(cond, val, max) by {}
        assert(cond.call(val));
        assert(!is_upper_bound_satisfy_cond(cond, val, max));
        assert(!forall|b: u64| #[trigger] cond.call(b) ==> b <= val);
        assert(exists|b: u64| #[trigger] cond.call(b) && b <= max && b > val);
        let val2 = choose|b: u64| #[trigger] cond.call(b) && b <= max && b > val;
        assert(val2 > val);
        assert(val2 <= max);
        lemma_has_conditional_upper_bound(val2, cond, max);
    }
}

pub proof fn proof_has_conditional_upper_bound<P: U64Predicate>(cond: &P, max: u64)
    ensures
        (exists|val| #[trigger] cond.call(val) && val <= max) ==> exists|val|
            is_upper_bound_satisfy_cond(cond, val, max),
{
    let exist_bound = exists|val| #[trigger] is_upper_bound_satisfy_cond(cond, val, max);
    let exist_val = exists|val| #[trigger] cond.call(val) && val <= max;
    if !exist_bound {
        assert forall|val| !is_upper_bound_satisfy_cond(cond, val, max) by {}
        if exist_val {
            let val = choose|val| #[trigger] cond.call(val) && val <= max;
            lemma_has_conditional_upper_bound(val, cond, max);
            assert(exist_bound);
        }
        assert(!exist_val);
    }
}

} // verus!
