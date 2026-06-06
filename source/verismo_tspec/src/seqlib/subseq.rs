use vstd::prelude::*;

verus! {

#[verifier(inline)]
pub open spec fn sub_element<T>(subs: Seq<T>, s: Seq<T>, idx: Seq<int>, k: int) -> bool {
    &&& (0 <= #[trigger] idx[k] < s.len())
    &&& (subs[k] === s[idx[k]])
}

pub open spec fn is_subseq_via_index<T>(subs: Seq<T>, s: Seq<T>, idx: Seq<int>) -> bool {
    &&& (forall|k: int| (0 <= k < idx.len()) ==> sub_element(subs, s, idx, k))
    &&& subs.len() == idx.len()
    &&& subs.len() <= s.len()
}

pub proof fn proof_empty_is_subs<T>(s: Seq<T>)
    ensures
        is_subseq_via_index(Seq::empty(), s, Seq::empty()),
{
}

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
}

pub proof fn lemma_remove_keep<T>(
    s: Seq<T>,
    keep: Seq<T>,
    removed: Seq<T>,
    keep_idx: Seq<int>,
    removed_idx: Seq<int>,
    i: int,
)  //-> (ret: (Seq<T>, Seq<T>, Seq<int>, Seq<int>))
    requires
        is_subseq_via_index(keep, s, keep_idx),
        is_subseq_via_index(removed, s, removed_idx),
        0 <= i < keep_idx.len(),
        keep.len() + removed.len() == s.len(),
    ensures
        is_subseq_via_index(keep.remove(i), s, keep_idx.remove(i)),
        is_subseq_via_index(
            removed.push(s[keep_idx[i]]),
            s,
            removed_idx.push(keep_idx[i]),
        ),
//ret === (keep.remove(i), removed.push(s[keep_idx[i]]), keep_idx.remove(i), removed_idx.push(keep_idx[i])),

{
    let keep0 = keep;
    let keep_idx0 = keep_idx;
    let (removed0, removed_idx0) = (removed, removed_idx);
    let removed1 = removed0.push(s[keep_idx0[i]]);
    let removed_idx1 = removed_idx0.push(keep_idx0[i]);
    let keep1 = keep0.remove(i);
    let keep_idx1 = keep_idx0.remove(i);
    proof_subs_remove(s, keep0, keep_idx0, i);
    proof_subs_push(s, removed0, removed_idx0, keep_idx0[i]);
}

} // verus!
