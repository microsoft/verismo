use super::*;

verus! {
    pub open spec fn is_upper_bound_satisfy_cond(cond_fn: spec_fn(u64) -> bool, bound: u64, max: u64) -> bool {
        &&& cond_fn(bound)
        &&& bound <= max
        &&& forall |b: u64| (#[trigger]cond_fn(b) && b <= max) ==> b <= bound
    }

    spec fn is_upper_bound(cond_fn: spec_fn(u64) -> bool, bound: u64, max: u64) -> bool {
        &&& bound <= max
        &&& forall |b: u64| (#[trigger]cond_fn(b) && b <= max) ==> b <= bound
    }

    proof fn lemma_has_conditional_upper_bound(val: u64, cond_fn: spec_fn(u64) -> bool, max: u64)
    requires
        cond_fn(val),
        val <= max,
    ensures
        exists|val| #[trigger] is_upper_bound_satisfy_cond(cond_fn, val, max)
    decreases
        max - val
    {
        let exist_bound = exists|val| #[trigger] is_upper_bound_satisfy_cond(cond_fn, val, max);
        if !exist_bound {
            assert forall |val| !is_upper_bound_satisfy_cond(cond_fn, val, max) by{}
            assert(cond_fn(val));
            assert(!is_upper_bound_satisfy_cond(cond_fn, val, max));
            assert(!forall |b: u64| #[trigger]cond_fn(b) ==> b <= val);
            assert(exists |b: u64| #[trigger]cond_fn(b) && b <= max && b > val);
            let val2 = choose |b: u64| #[trigger]cond_fn(b) && b <= max && b > val;
            assert(val2 > val);
            assert(val2 <= max);
            lemma_has_conditional_upper_bound(val2, cond_fn, max);
        }

    }

    pub proof fn proof_has_conditional_upper_bound(cond_fn: spec_fn(u64) -> bool, max: u64)
    ensures
        (exists|val| #[trigger]cond_fn(val) && val <= max) ==> exists|val| is_upper_bound_satisfy_cond(cond_fn, val, max)
    {
        let exist_bound = exists|val| #[trigger] is_upper_bound_satisfy_cond(cond_fn, val, max);
        let exist_val = exists|val| #[trigger] cond_fn(val) && val <= max;
        if !exist_bound {
            assert forall |val| !is_upper_bound_satisfy_cond(cond_fn, val, max) by{}
            if exist_val {
                let val = choose |val| #[trigger]cond_fn(val) && val <= max;
                lemma_has_conditional_upper_bound(val, cond_fn, max);
                assert(exist_bound);
            }
            assert(!exist_val);
        }
    }
}
