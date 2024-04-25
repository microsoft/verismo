use vstd::prelude::*;
use vstd::set_lib;

use super::*;

verus! {

pub proof fn lemma_ret_is_empty<A>(s: Set<A>) -> (b: bool)
    ensures
        b <==> s.finite() && s.len() == 0,
        b <==> s =~= Set::empty(),
{
    if s.finite() && s.len() == 0 {
        s.lemma_len0_is_empty();
    }
    s =~= Set::empty()
}

pub proof fn lemma_union_self<A>(s1: Set<A>)
    ensures
        s1.union(s1) =~~= s1,
{
}

pub proof fn lemma_union<A>(s1: Set<A>, s2: Set<A>)
    ensures
        s1.subset_of(s1.union(s2)),
        s2.subset_of(s1.union(s2)),
        s1.union(s2) =~~= (s2.union(s1)),
        s1.union(s2) =~~= (s1.union(s2).union(s2)),
{
    let ss1 = s1;
    let ss2 = s1.union(s2);
    assert forall|a: A| ss1.contains(a) implies ss2.contains(a) by {}
}

pub open spec fn convert_set<A, B>(s: Set<A>, f: spec_fn(B) -> A) -> Set<B> {
    Set::new(|a| s.contains(f(a)))
}

pub open spec fn uop_to_bop<T1, T2, T3>(op: spec_fn(T1) -> T3) -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| op(v1)
}

#[verifier(inline)]
pub open spec fn set_op<T1, T2, T3>(s1: Set<T1>, s2: Set<T2>, op_fn: spec_fn(T1, T2) -> T3) -> Set<
    T3,
> {
    Set::new(|val: T3| exists|v1, v2| s1.contains(v1) && s2.contains(v2) && val === op_fn(v1, v2))
}

#[verifier(inline)]
pub open spec fn set_uop<T1, T2>(s1: Set<T1>, op_fn: spec_fn(T1) -> T2) -> Set<T2> {
    Set::new(
        |val: T2| exists|v1| s1.contains(v1) && val === op_fn(v1),
    )
    //set_op(s1, Set::empty().insert(arbitrary::<T1>()), uop_to_bop(op_fn))

}

spec fn set_bop_recursive<T1, T2, T3>(
    s1: Set<T1>,
    s2: Set<T2>,
    op_fn: spec_fn(T1, T2) -> T3,
) -> Set<T3>
    recommends
        s1.finite(),
    decreases s1.len(),
{
    if s1.finite() {
        if !s1.is_empty() {
            let ss1 = s1.remove(s1.choose());
            if (ss1.len() < s1.len()) {
                set_bop_recursive(ss1, s2, op_fn).union(set_op1(s1.choose(), s2, op_fn))
            } else {
                // unreacheable
                Set::empty()
            }
        } else {
            Set::empty()
        }
    } else {
        Set::empty()
    }
}

#[verifier(inline)]
spec fn set_op1<T1, T2, T3>(v1: T1, s2: Set<T2>, op_fn: spec_fn(T1, T2) -> T3) -> Set<T3> {
    set_uop(s2, |v2| op_fn(v1, v2))
}

proof fn lemma_setop1<T1, T2, T3>(v1: T1, s2: Set<T2>, op_fn: spec_fn(T1, T2) -> T3) -> (ret: Set<
    T3,
>)
    requires
        s2.finite(),
    ensures
        ret =~~= set_op1(v1, s2, op_fn),
        ret.len() <= s2.len(),
        ret.finite(),
    decreases s2.len(),
{
    let ret = set_op1(v1, s2, op_fn);
    lemma_set_uop_len(s2, |v2| op_fn(v1, v2));
    ret
}

// when op_fn is a loseless function
proof fn lemma_setop_without_loss_disjoint<T1, T2, T3>(
    s1: Set<T1>,
    s2: Set<T2>,
    vv1: T1,
    op_fn: spec_fn(T1, T2) -> T3,
    reverse_op_fn: spec_fn(T3) -> (T1, T2),
)
    requires
        s1.len() > 0,
        s1.contains(vv1),
        forall|v1, v2| reverse_op_fn(#[trigger] op_fn(v1, v2)) == (v1, v2),
    ensures
        set_op1(vv1, s2, op_fn).disjoint(set_op(s1.remove(vv1), s2, op_fn)),
{
    let ss1 = s1.remove(vv1);
    let r1 = set_op(ss1, s2, op_fn);
    let r2 = set_op1(vv1, s2, op_fn);
    assert forall|val|
        (r1.contains(val) ==> !r2.contains(val)) && (r2.contains(val) ==> !r1.contains(val)) by {
        if r1.contains(val) {
            let (v1, v2) = choose|v1, v2|
                ss1.contains(v1) && s2.contains(v2) && val === op_fn(v1, v2);
            assert(ss1.contains(v1));
            assert(vv1 !== v1);
            assert(op_fn(v1, v2) === val);
            assert(reverse_op_fn(val) === (v1, v2));
        }
        if r2.contains(val) {
            let v2 = choose|v2| s2.contains(v2) && val === op_fn(vv1, v2);
            assert(reverse_op_fn(val) === (vv1, v2));
        }
    }
}

proof fn lemma_setop_3_union<T1, T2, T3>(
    s1: Set<T1>,
    s2: Set<T2>,
    op_fn: spec_fn(T1, T2) -> T3,
    vv1: T1,
) -> (ret: (Set<T3>, Set<T3>, Set<T3>))
    requires
        s1.len() > 0,
        s1.contains(vv1),
        s1.finite(),
        s2.finite(),
    ensures
        ret.0 =~~= set_op(s1, s2, op_fn),
        ret.1 =~~= set_op(s1.remove(vv1), s2, op_fn),
        ret.2 =~~= set_op1(vv1, s2, op_fn),
        ret.0 =~~= ret.1.union(ret.2),
{
    let r0 = set_op(s1, s2, op_fn);
    let r1 = set_op(s1.remove(vv1), s2, op_fn);
    let r2 = lemma_setop1(vv1, s2, op_fn);
    let ss1 = s1.remove(vv1);
    assert forall|val| #[trigger] r0.contains(val) == r1.union(r2).contains(val) by {
        if r0.contains(val) {
            let (v1, v2) = choose|v1, v2|
                s1.contains(v1) && s2.contains(v2) && val === op_fn(v1, v2);
            assert(s1.contains(v1) && s2.contains(v2) && val === op_fn(v1, v2));
            if (ss1.contains(v1)) {
                assert(r1.contains(val));
            } else {
                if (v1 != vv1) {
                    assert(ss1.contains(v1));
                } else {
                    assert(r2.contains(val));
                }
            }
        }
        if (r1.contains(val)) {
            let (v1, v2) = choose|v1, v2|
                ss1.contains(v1) && s2.contains(v2) && val === op_fn(v1, v2);
            assert(s1.contains(v1) && s2.contains(v2) && val === op_fn(v1, v2));
            assert(r0.contains(val))
        }
        if (r2.contains(val)) {
            let v2 = choose|v2| s2.contains(v2) && val === op_fn(vv1, v2);
            assert(s1.contains(vv1) && s2.contains(v2) && val === op_fn(vv1, v2));
            assert(r0.contains(val));
        }
    }
    (r0, r1, r2)
}

pub open spec fn exchange_spec_fn<T1, T2, T3>(op_fn: spec_fn(T1, T2) -> T3) -> spec_fn(
    T2,
    T1,
) -> T3 {
    |v1, v2| op_fn(v2, v1)
}

pub proof fn lemma_op_exchange<T1, T2, T3>(
    s1: Set<T1>,
    s2: Set<T2>,
    op_fn: spec_fn(T1, T2) -> T3,
) -> (ret: Set<T3>)
    requires
        s1.len() > 0,
        s1.finite(),
        s2.finite(),
    ensures
        ret =~~= set_op(s1, s2, op_fn),
        ret =~~= set_op(s2, s1, exchange_spec_fn(op_fn)),
{
    set_op(s1, s2, op_fn)
}

pub proof fn lemma_set_uop_len<T1, T2>(s1: Set<T1>, op_fn: spec_fn(T1) -> T2) -> (ret: Set<T2>)
    requires
        s1.finite(),
    ensures
        ret =~~= set_uop(s1, op_fn),
        (ret.len() == 0) == (s1.len() == 0),
        ret.len() <= s1.len(),
        ret.finite(),
    decreases s1.len(),
{
    let ret = set_uop(s1, op_fn);
    if !s1.is_empty() {
        let v1 = s1.choose();
        let prev = lemma_set_uop_len(s1.remove(v1), op_fn);
        assert(ret =~~= prev.insert(op_fn(v1)));
        assert(!ret.is_empty());
    } else {
        assert(s1.is_empty());
        assert forall|v| !ret.contains(v) by {};
        assert(ret =~~= Set::empty());
        assert(ret.is_empty());
    }
    ret
}

proof fn lemma_set_bop_len_recursive<T1, T3, T2>(
    s1: Set<T1>,
    s2: Set<T2>,
    op_fn: spec_fn(T1, T2) -> T3,
) -> (ret: Set<T3>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        ret =~~= set_bop_recursive(s1, s2, op_fn),
        (ret.len() == 0) == (s1.len() == 0 || s2.len() == 0),
        ret.len() <= s1.len() * s2.len(),
        ret.finite(),
    decreases s1.len(),
{
    let ret = set_bop_recursive(s1, s2, op_fn);
    if !s1.is_empty() {
        let v1 = s1.choose();
        let ss1 = s1.remove(v1);
        let r1 = lemma_set_bop_len_recursive(s1.remove(v1), s2, op_fn);
        let r2 = set_op1(v1, s2, op_fn);
        assert(ret =~~= r1.union(r2));
        let uop_fn = |v2| op_fn(v1, v2);
        assert(set_op1(v1, s2, op_fn) =~~= set_uop(s2, uop_fn));
        lemma_set_uop_len(s2, uop_fn);
        set_lib::lemma_len_union(r1, r2);
        assert(r2.len() <= s2.len()) by {
            lemma_setop1(v1, s2, op_fn);
        }
        assert(ss1.len() * s2.len() + s2.len() == s1.len() * s2.len()) by {
            proof_mul_assoc(ss1.len(), 1, s2.len());
            proof_mul_exchange(s2.len() as int, s1.len() as int);
            proof_mul_exchange(ss1.len() as int, s2.len() as int);
        }
        if s2.is_empty() {
            assert(ret.is_empty());
        } else {
            assert(!ret.is_empty()) by { assert(ret.contains(op_fn(s1.choose(), s2.choose()))) }
        }
    } else {
        assert(s1.len() * s2.len() == 0) by (nonlinear_arith)
            requires
                s1.len() == 0 || s2.len() == 0,
        ;
        assert(ret.is_empty());
    }
    ret
}

proof fn lemma_setop_eq_recursive<T1, T2, T3>(
    s1: Set<T1>,
    s2: Set<T2>,
    op_fn: spec_fn(T1, T2) -> T3,
) -> (ret: Set<T3>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        ret =~~= set_op(s1, s2, op_fn),
        ret =~~= set_bop_recursive(s1, s2, op_fn),
    decreases s1.len(),
{
    let ret = set_op(s1, s2, op_fn);
    if !s1.is_empty() {
        let prev = lemma_setop_eq_recursive(s1.remove(s1.choose()), s2, op_fn);
        assert(ret =~~= prev.union(set_op1(s1.choose(), s2, op_fn))) by {
            lemma_setop_3_union(s1, s2, op_fn, s1.choose());
        }
    } else {
        assert(ret =~~= Set::empty());
    }
    ret
}

pub proof fn lemma_setop_len<T1, T2, T3>(
    s1: Set<T1>,
    s2: Set<T2>,
    op_fn: spec_fn(T1, T2) -> T3,
) -> (ret: Set<T3>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        ret =~~= set_op(s1, s2, op_fn),
        (ret.len() == 0) == (s1.len() == 0 || s2.len() == 0),
        ret.len() <= s1.len() * s2.len(),
        ret.finite(),
{
    let ret = set_op(s1, s2, op_fn);
    lemma_setop_eq_recursive(s1, s2, op_fn);
    lemma_set_bop_len_recursive(s1, s2, op_fn);
    ret
}

pub proof fn lemma_seq_add_subrange<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        (s1 + s2).subrange(s1.len() as int, (s1 + s2).len() as int) =~~= s2,
;

} // verus!
