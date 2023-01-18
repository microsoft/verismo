use vstd::multiset::Multiset;
use vstd::seq_lib::{lemma_multiset_commutative, lemma_seq_union_to_multiset_commutative};

use super::*;
verus! {
    pub open spec fn seq_is_sorted<T>(s: Seq<T>, speclt: spec_fn(T, T) -> bool) -> bool {
        forall |i: int, j: int| 0 <= i < j < s.len()
            ==> !speclt(#[trigger]s[j], #[trigger]s[i])
    }

    pub proof fn proof_sorted_subrange<T>(s: Seq<T>, speclt: spec_fn(T, T) -> bool, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        seq_is_sorted(s, speclt) ==> seq_is_sorted(s.subrange(start, end), speclt)
    {
        let ret = s.subrange(start, end);
        if seq_is_sorted(s, speclt) {
            assert forall |i: int, j: int| 0 <= i < j < ret.len()
            implies !speclt(#[trigger]ret[j], #[trigger]ret[i])
            by {
                assert(!speclt(s[j], s[i]));
            }
        }
    }

    pub proof fn seq_to_multi_set_to_set<T>(s1: Seq<T>)
    ensures
        s1.to_set() === s1.to_multiset().dom()
    {
        s1.to_multiset_ensures();
        assert(s1.to_set() =~~= s1.to_multiset().dom()) by {
            assert forall |a| s1.contains(a) == s1.to_multiset().dom().contains(a) by{
                assert(s1.contains(a) == (s1.to_multiset().count(a) > 0));
            }
        }
    }

    pub open spec fn seq_uop<A, B>(s: Seq<A>, op: spec_fn(A) -> B) -> Seq<B> {
        Seq::new(s.len(), |i| op(s[i]))
    }

    pub proof fn proof_seq_to_multiset_insert<A>(s1: Seq<A>, i: int, v: A)
    requires
        0 <= i <= s1.len(),
    ensures
        s1.insert(i, v).to_multiset() === s1.to_multiset().insert(v)
    {
        let s2 = s1.insert(i, v);
        let left = s1.take(i);
        let middle = Seq::empty().push(v);
        let left2 = left + middle;
        let right = s1.skip(i);
        assert(s1 =~~= left + right);
        assert(s2 =~~= left + middle + right);
        assert(s2 === left2 + right);
        if i < s1.len() {
            left.to_multiset_ensures();
            lemma_multiset_commutative(left, middle);
            lemma_multiset_commutative(left2, right);
            lemma_seq_union_to_multiset_commutative(left2, right);
              lemma_seq_union_to_multiset_commutative(left, right);
            lemma_multiset_commutative(left + right, middle);
            lemma_multiset_commutative(left, right);
            (left + right).to_multiset_ensures();
            assert(left + right =~~= s1);
            assert(s1 + middle =~~= s1.push(v));
            s1.to_multiset_ensures();
            assert(s2.to_multiset() === (left2 + right).to_multiset());
            assert((left2 + right).to_multiset() === (right + left2).to_multiset());
            assert(left2.to_multiset() === left.to_multiset().add(middle.to_multiset()));
            // multiset distribution property
            assert((right + left2).to_multiset() =~~= right.to_multiset().add(left.to_multiset()).add(middle.to_multiset()));
            assert(s1.to_multiset().add(middle.to_multiset()) =~~= right.to_multiset().add(left.to_multiset()).add(middle.to_multiset()));
            assert(s2.to_multiset() === (left + right + middle).to_multiset());
        } else {
            assert(s2 =~~= s1.push(v));
            s1.to_multiset_ensures();
            assert(s1.insert(i, v).to_multiset() === s1.to_multiset().insert(v));
        }
    }

    //#[verifier(external_body)]
    pub proof fn proof_seq_to_seq_eq_multiset<A, B>(s1: Seq<A>, s2: Seq<A>, op: spec_fn(A) -> B)
    requires
        s1.to_multiset() === s2.to_multiset(),
        s1.len() == s2.len(),
    ensures
        seq_uop(s1, op).to_multiset() === seq_uop(s2, op).to_multiset(),
    decreases
        s1.len()
    {
        if s1.len() > 0 {
            let v = s1.last();
            let ss1 = s1.drop_last();
            assert(s1 =~~= ss1.push(v));
            s1.to_multiset_ensures();
            s2.to_multiset_ensures();
            assert(s1[s1.len() - 1] == v);
            assert(s1.contains(v));
            assert(s1.to_multiset().count(v) > 0);
            assert(s2.contains(v));
            let i = choose |i| s2[i] === v && 0 <= i < s2.len();
            let ss2 = s2.remove(i);
            assert(s2 =~~= ss2.insert(i, v));
            assert(seq_uop(s2, op) =~~= seq_uop(ss2, op).insert(i, op(v)));
            proof_seq_to_multiset_insert(seq_uop(ss2, op), i, op(v));
            assert(seq_uop(ss1, op).push(op(v)) =~~= seq_uop(s1, op));
            seq_uop(ss1, op).to_multiset_ensures();
            proof_seq_to_multiset_insert(ss2, i, v);
            ss1.to_multiset_ensures();
            assert(ss2.to_multiset().insert(v) =~~= s2.to_multiset());
            assert(ss1.to_multiset().insert(v) =~~= s1.to_multiset());
            assert(ss2.to_multiset() =~~= s2.to_multiset().remove(v));
            assert(ss1.to_multiset() =~~= s1.to_multiset().remove(v));
            assert(ss1.to_multiset() =~~= ss2.to_multiset());
            proof_seq_to_seq_eq_multiset(ss1, ss2, op);
        } else {
            assert(s1 =~~= s2);
        }
    }
}
