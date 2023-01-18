use vstd::prelude::*;

verus! {
    #[verifier(inline)]
    pub open spec fn sub_element<T>(subs: Seq<T>, s: Seq<T>, idx: Seq<int>, k: int) -> bool
    {
        &&& (0 <= #[trigger]idx[k] < s.len())
        &&& (subs[k] === s[idx[k]])
    }

    pub open spec fn is_subseq_via_index<T>(subs: Seq<T>, s: Seq<T>, idx: Seq<int>) -> bool
    {
        &&& (forall |k: int| (0<= k < idx.len()) ==> sub_element(subs, s, idx, k))
        &&& subs.len() == idx.len()
        &&& subs.len() <= s.len()
    }

    pub proof fn proof_empty_is_subs<T>(s: Seq<T>)
    ensures
        is_subseq_via_index(Seq::empty(), s, Seq::empty())
    {}

    pub proof fn proof_subs_remove<T>(s: Seq<T>, subs: Seq<T>, subs_idx: Seq<int>, i: int)
    requires
        is_subseq_via_index(subs, s, subs_idx),
        0 <= i < subs_idx.len(),
    ensures
        is_subseq_via_index(subs.remove(i), s, subs_idx.remove(i)),
        subs.remove(i).len() == subs.len() - 1,
    {
        let (subs0, subs_idx0) = (subs, subs_idx);
        let subs1 = subs0.remove(i);
        let subs_idx1 = subs_idx0.remove(i);
        assert forall |k: int| (0<= k < subs_idx1.len())
        implies
            sub_element(subs1, s, subs_idx1, k)
        by{
            assert(subs_idx1.len() == subs_idx0.len() - 1);
            assert(0 <= k < subs_idx0.len());
            assert(0 <= k < subs0.len());
            assert(0 <= k < subs1.len());
            if k < i {
                assert(sub_element(subs0, s, subs_idx0, k));
                assert(subs_idx0[k] == subs_idx1[k]);
                assert(subs0[k] === subs1[k]);
                assert(sub_element(subs1, s, subs_idx1, k));
            } else {
                assert(subs_idx0[k + 1] == subs_idx1[k]);
                assert(subs0[k + 1] === subs1[k]);
                assert(sub_element(subs0, s, subs_idx0, k + 1));
                assert(sub_element(subs1, s, subs_idx1, k));
            }
        }
        assert(subs1.len() == subs_idx1.len());
        assert(subs1.len() <= s.len());
    }

    pub proof fn proof_subs_push<T>(s: Seq<T>, subs: Seq<T>, subs_idx: Seq<int>, i: int)
    requires
        is_subseq_via_index(subs, s, subs_idx),
        0 <= i < s.len(),
        subs.len() < s.len(),
    ensures
        is_subseq_via_index(subs.push(s[i]), s, subs_idx.push(i)),
        subs.push(s[i]).len() == subs.len() + 1,
        subs_idx.push(i).len() == subs_idx.len() + 1,
    {
        let (subs0, subs_idx0) = (subs, subs_idx);
        let subs1 = subs.push(s[i]);
        let subs_idx1 = subs_idx.push(i);
        assert(subs_idx1.len() == subs_idx0.len() + 1);
        assert forall |k: int| (0<= k < subs_idx1.len())
        implies
            sub_element(subs1, s, subs_idx1, k)
        by{
            assert(subs_idx1.len() == subs_idx0.len() + 1);
            if (0 <= k < subs_idx0.len()) {
                assert(0 <= k < subs0.len());
                assert(0 <= k < subs1.len());
                assert(sub_element(subs0, s, subs_idx0, k));
                assert(subs_idx0[k] == subs_idx1[k]);
                assert(subs0[k] === subs1[k]);
                assert(sub_element(subs1, s, subs_idx1, k));
            } else {
                assert(k == subs_idx0.len());
                assert(i == subs_idx1[k]);
                assert(s[i] === subs1[k]);
                assert(sub_element(subs1, s, subs_idx1, k));
            }
        }
        assert(subs1.len() == subs_idx1.len());
        assert(subs1.len() <= s.len());
        assert(is_subseq_via_index(subs1, s, subs_idx1));
    }

    pub proof fn lemma_remove_keep<T>(s: Seq<T>, keep: Seq<T>, removed: Seq<T>, keep_idx: Seq<int>, removed_idx: Seq<int>, i: int) //-> (ret: (Seq<T>, Seq<T>, Seq<int>, Seq<int>))
    requires
        is_subseq_via_index(keep, s, keep_idx),
        is_subseq_via_index(removed, s, removed_idx),
        0 <= i < keep_idx.len(),
        keep.len() + removed.len() == s.len(),
    ensures
        is_subseq_via_index(keep.remove(i), s, keep_idx.remove(i)),
        is_subseq_via_index(removed.push(s[keep_idx[i]]), s, removed_idx.push(keep_idx[i])),
        //ret === (keep.remove(i), removed.push(s[keep_idx[i]]), keep_idx.remove(i), removed_idx.push(keep_idx[i])),
    {
        let keep0 = keep;
        let keep_idx0 = keep_idx;
        let (removed0, removed_idx0) = (removed, removed_idx);
        assert(sub_element(keep0, s, keep_idx0, i));
        assert(0 <= keep_idx0[i] < s.len());

        let removed1 = removed0.push(s[keep_idx0[i]]);
        let removed_idx1 = removed_idx0.push(keep_idx0[i]);
        let keep1 = keep0.remove(i);
        let keep_idx1 = keep_idx0.remove(i);
        proof_subs_remove(s, keep0, keep_idx0, i);
        proof_subs_push(s, removed0, removed_idx0, keep_idx0[i]);
    }

    pub proof fn proof_remove_keep<T>(s: Seq<T>, keep: Seq<T>, removed: Seq<T>, keep_idx: &mut Seq<int>, removed_idx: &mut Seq<int>, i: int)
    requires
        is_subseq_via_index(keep, s, *old(keep_idx)),
        is_subseq_via_index(removed, s, *old(removed_idx)),
        0 <= i < old(keep_idx).len(),
        keep.len() + removed.len() == s.len(),
    ensures
        is_subseq_via_index(keep.remove(i), s, *keep_idx),
        is_subseq_via_index(removed.push(s[old(keep_idx)[i]]), s, *removed_idx),
        *keep_idx === (old(keep_idx).remove(i)),
        *removed_idx === old(removed_idx).push(old(keep_idx)[i]),
    {
        let (keep0, keep_idx0) = (keep, *keep_idx);
        let (removed0, removed_idx0) = (removed, *removed_idx);
        assert(sub_element(keep0, s, keep_idx0, i));
        assert(0 <= keep_idx0[i] < s.len());

        let removed1 = removed0.push(s[keep_idx0[i]]);
        let removed_idx1 = removed_idx0.push(keep_idx0[i]);
        let keep1 = keep0.remove(i);
        let keep_idx1 = keep_idx0.remove(i);
        proof_subs_remove(s, keep0, keep_idx0, i);
        proof_subs_push(s, removed0, removed_idx0, keep_idx0[i]);
        *keep_idx = keep_idx1;
        *removed_idx = removed_idx1;
    }
}
