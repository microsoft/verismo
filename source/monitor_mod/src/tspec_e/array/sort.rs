use vstd::multiset::Multiset;
use vstd::seq_lib::*;

use super::array_utils::*;
use super::*;

verus! {
proof fn lemma_seq_to_multiset_swap<T>(input: Seq<T>, i: int, j: int) -> (ret: Seq<T>)
requires
    0 <= i < input.len(),
    0 <= j < input.len(),
ensures
    ret === spec_swap(input, i, j),
    ret.to_multiset() =~~= input.to_multiset(),
{
    let ret = spec_swap(input, i, j);
    input.to_multiset_ensures();
    lemma_seq_to_multiset_update(input, i, input[j]);
    lemma_seq_to_multiset_update(input.update(i, input[j]), j, input[i]);
    input.update(i, input[j]).to_multiset_ensures();

    input.to_multiset().remove(input[i]).insert(input[j]).remove(input[j]).insert(input[i]);
    ret
}

proof fn lemma_seq_to_multiset_update<T>(input: Seq<T>, i: int, v: T)
requires
    0 <= i < input.len(),
ensures
    input.update(i, v).to_multiset() =~~= input.to_multiset().remove(input[i]).insert(v),
{
    let ret = input.update(i, v);
    let left = input.subrange(0, i);
    let u = input[i];
    let right = input.subrange(i + 1, input.len() as int);
    assert(ret =~~= left.push(v) + right);
    assert(input =~~= left.push(u) + right);
    lemma_multiset_commutative(left.push(v), right);
    lemma_multiset_commutative(left.push(u), right);
    left.to_multiset_ensures();
    assert(left.push(v).to_multiset() =~~= left.to_multiset().add(Multiset::singleton(v)));
    assert(left.push(u).to_multiset() =~~= left.to_multiset().add(Multiset::singleton(u)));
    assert(ret.to_multiset() =~~= left.push(v).to_multiset().add(right.to_multiset()));
    assert(input.to_multiset() =~~= left.push(u).to_multiset().add(right.to_multiset()));
    assert(ret.to_multiset() =~~= left.to_multiset().add(Multiset::singleton(u)).add(right.to_multiset()).remove(u).add(Multiset::singleton(v)));
}

proof fn proof_seq_to_multiset_update<T>(input: Seq<T>, i: int, v: T)
requires
    0 <= i < input.len(),
ensures
    input.to_multiset().contains(input[i]),
    input.update(i, v).to_multiset() =~~= (input.to_multiset().remove(input[i]).insert(v)),
{
    lemma_seq_to_multiset_update(input, i, v);
    input.to_multiset_ensures();
}

proof fn proof_seq_update_in_subrange<T>(input: Seq<T>, start: int, end: int, i: int, v: T)
requires
    0 <= start <= i < end <= input.len(),
ensures
    input.update(i, v).subrange(start, end) =~~= input.subrange(start, end).update(i - start, v)
{
    assert(input.update(i, v).subrange(start, end)[i-start] === v);
}

proof fn proof_seq_swap_in_subrange<T>(input: Seq<T>, start: int, end: int, i: int, j: int)
requires
    0 <= start <= i < end <= input.len(),
    0 <= start <= j < end <= input.len(),
ensures
    spec_swap(input, i, j).subrange(start, end) =~~= spec_swap(input.subrange(start, end), i - start,  j - start)
{
    let v = input[i];
    let u = input[j];
    assert(input.subrange(start, end)[i-start] === v);
    assert(input.subrange(start, end)[j-start] === u);
    proof_seq_update_in_subrange(input, start, end, i, input[i]);
    assert(input.update(i, v).subrange(start, end) =~~= input.subrange(start, end).update(i - start, v));
    proof_seq_update_in_subrange(input.update(i, v), start, end, j, u);
    assert(input.update(i, v).update(j, u).subrange(start, end) =~~= input.update(i, v).subrange(start, end).update(j - start, u));
    assert(input.update(i, v).subrange(start, end).update(j - start, u) =~~= input.subrange(start, end).update(i - start, v).update(j - start, u));
}

pub open spec fn spec_less_fn_requires<T, F: FnOnce(T, T) -> bool>(less: F, speclt: spec_fn(T, T) -> bool, s: Seq<T>) -> bool {
    // all elements meets the requires
    &&& forall |x, y| s.contains(x) && s.contains(y) ==> #[trigger] less.requires((x, y))
    // less and speclt relationship
    &&& forall |x, y, r| less.ensures((x, y), r) ==> (speclt(x, y) == r)
    // spec_lt properties
    &&& forall |x, y| #[trigger] speclt(x, y) ==> !speclt(y, x)
    &&& forall |x| ! #[trigger] speclt(x, x)
    &&& forall |x, y, z| #[trigger]speclt(x, y) && !#[trigger]speclt(z, y) ==> speclt(x, z)
    &&& forall |x, y, z| !#[trigger]speclt(x, y) && !#[trigger]speclt(y, z) ==> !speclt(x, z)

}
}

verus! {
impl<T: Copy, const N: IndexType> Array<T, N> {
        fn partition<F>(&mut self, start: usize_t, end: usize_t, less: F, Ghost(speclt): Ghost<spec_fn(T, T) -> bool>) -> (ret: usize_t)
        where F: FnOnce(T, T) -> bool + core::marker::Copy
        requires
            spec_less_fn_requires(less, speclt, old(self)@.subrange(start as int, end as int)),
            0 <= (start as int) < (end as int) <= Self::spec_len(),
            start.is_constant(),
            end.is_constant(),
        ensures
            forall |k: int| (ret as int) <= k < end as int ==> !speclt(#[trigger]self@[k], self@[ret as int]),
            forall |k: int| (start as int) <= k < ret as int ==> speclt(#[trigger]self@[k], self@[ret as int]),
            forall |k: int| 0 <= k < (start as int) || (end as int) <= k < Self::spec_len() ==> self@[k] === old(self)@[k], // unchanged elements
            old(self)@.to_multiset() =~~= self@.to_multiset(),
            old(self)@.subrange(start as int, end as int).to_multiset() =~~= self@.subrange(start as int, end as int).to_multiset(),
            start as int <= (ret as int) < (end as int),
            ret.is_constant(),
        {
            let pivot_index = end - 1;
            proof {
                lemma_seq_to_multiset_swap(self@, pivot_index as int, (end as int - 1));
                proof_seq_swap_in_subrange(self@, start as int, end as int, pivot_index as int, end as int - 1);
                lemma_seq_to_multiset_swap(self@.subrange(start as int, end as int), pivot_index as int - start as int, (end as int - 1 - start as int));
            }
            self.swap(pivot_index, end - 1);

            let mut i = start;
            let mut j = start;
            let last = end - 1;
            while j < last
            invariant
                i.is_constant(),
                j.is_constant(),
                start.is_constant(),
                last.is_constant(),
                last as int == end as int - 1,
                0 <= (start as int) <= (last as int) < (end as int),
                0 <= (start as int) < (end as int) <= Self::spec_len(),
                start as int <= (j as int) <= (last as int),
                (start as int) <= (i as int) <= (j as int),
                spec_less_fn_requires(less, speclt, self@.subrange(start as int, end as int)),
                forall |k: int| (start as int) <= k < i as int ==> speclt(#[trigger]self@[k], self@[last as int]),
                forall |k: int| (i as int) <= k < (j as int) ==> !speclt(#[trigger]self@[k], self@[last as int]),
                forall |k: int| 0 <= k < (start as int) || (end as int) <= k < Self::spec_len() ==> self@[k] === old(self)@[k],
                old(self)@.to_multiset() =~~= self@.to_multiset(),
                old(self)@.subrange(start as int, end as int).to_multiset() =~~= self@.subrange(start as int, end as int).to_multiset(),
            {
                proof {
                    assert(self@.len() == Self::spec_len());
                    self@.to_multiset_ensures();
                    let targets = self@.subrange(start as int, end as int);
                    targets.to_multiset_ensures();
                    assert(self[j as int] === targets[j as int - (start as int)]);
                    assert(self[last as int] === targets[last as int - (start as int)]);
                    assert(targets.contains(self[j as int]));
                    assert(targets.contains(self[last as int]));
                }
                if less(*self.index(j), *self.index(last)) {
                    proof {
                        lemma_seq_to_multiset_swap(self@, i as int, j as int);
                        proof_seq_swap_in_subrange(self@, start as int, end as int, i as int, j as int);
                        lemma_seq_to_multiset_swap(self@.subrange(start as int, end as int), i as int - start as int, j as int - start as int);
                    }
                    self.swap(i, j);
                    i = i + 1;
                }
                j = j + 1;
            }
            proof {
                lemma_seq_to_multiset_swap(self@, i as int, j as int);
                proof_seq_swap_in_subrange(self@, start as int, end as int, i as int, last as int);
                lemma_seq_to_multiset_swap(self@.subrange(start as int, end as int), i as int - start as int, last as int - start as int);
            }
            self.swap(i, last);

            i
        }

        pub fn sort<F>(&mut self, start: usize, end: usize, less: F, Ghost(speclt): Ghost<spec_fn(T, T) -> bool>)
        where F: FnOnce(T, T) -> bool + core::marker::Copy
        requires
            spec_less_fn_requires(less, speclt, old(self)@.subrange(start as int, end as int)),
            0 <= (start as int) <= (end as int) <= Self::spec_len(),
            start.is_constant(),
            end.is_constant(),
        ensures
            seq_is_sorted(self@.subrange(start as int, end as int), speclt),
            forall |i: int, j: int| start as int <= i < j < end as int ==> !speclt(#[trigger]self@[j], #[trigger]self@[i]),
            forall |k: int| 0 <= k < (start as int) || (end as int) <= k < Self::spec_len() ==> self@[k] === old(self)@[k],
            old(self)@.subrange(start as int, end as int).to_multiset() =~~= self@.subrange(start as int, end as int).to_multiset(),
            old(self)@.to_multiset() =~~= self@.to_multiset(),
        decreases
            end as int - start as int,
        {
            if start >= end || start + 1 >= end {
                return;
            }
            let ghost s0 = self@;
            let ghost ss0 = s0.subrange(start as int, end as int);
            proof {
                self@.to_multiset_ensures();
                self@.subrange(start as int, end as int).to_multiset_ensures();
            }
            let pivot_index = self.partition(start, end, less, Ghost(speclt));
            let ghost s1 = self@;
            let ghost ss1 = s1.subrange(start as int, end as int);
            let ghost (s1_left, s1_right) = (
                s1.subrange(start as int, pivot_index as int),
                s1.subrange(pivot_index as int + 1, end as int)
            );
            let ghost s1_right2 = s1.subrange(pivot_index as int, end as int);
            proof {
                s1.to_multiset_ensures();
                ss1.to_multiset_ensures();
                s1_left.to_multiset_ensures();
                s1_right.to_multiset_ensures();
                assert forall |x, y| ss1.contains(x) && ss1.contains(y)
                implies #[trigger] less.requires((x, y)) by {
                    assert(ss1.to_multiset().count(x) > 0);
                    assert(ss1.to_multiset().count(y) > 0);
                    assert(ss0.contains(x));
                    assert(ss0.contains(y));
                }
                assert forall |x| s1_left.contains(x)
                implies ss1.contains(x)
                by {
                    let i = choose|i: int| 0 <= i < s1_left.len() && s1_left[i] === x;
                    assert(ss1[i] === s1_left[i]);
                    assert(ss1.contains(x));
                }
                assert forall |x, y| s1_left.contains(x) && s1_left.contains(y)
                implies #[trigger] less.requires((x, y)) by {
                    assert(ss1.contains(x));
                    assert(ss1.contains(y));
                }
            }
            if start + 1 < pivot_index  {
                self.sort(start, pivot_index, less, Ghost(speclt));
            }
            let ghost s2 = self@;
            let ghost ss2 = s2.subrange(start as int, end as int);
            let ghost (s2_left, s2_right) = (
                s2.subrange(start as int, pivot_index as int),
                s2.subrange(pivot_index as int + 1, end as int)
            );
            let ghost s2_right2 = s2.subrange(pivot_index as int, end as int);
            proof {
                s2.to_multiset_ensures();
                ss2.to_multiset_ensures();
                s2_left.to_multiset_ensures();
                s2_right.to_multiset_ensures();
                assert(ss1 =~~= s1_left + s1_right2);
                assert(ss2 =~~= s2_left + s2_right2);
                assert(s1_right2 =~~= s2_right2);
                lemma_multiset_commutative(s1_left, s1_right2);
                lemma_multiset_commutative(s2_left, s2_right2);
                assert forall |x, y| ss2.contains(x) && ss2.contains(y)
                implies #[trigger] less.requires((x, y)) by {
                    assert(ss2.to_multiset().count(x) > 0);
                    assert(ss2.to_multiset().count(y) > 0);
                    assert(ss1.contains(x));
                    assert(ss1.contains(y));
                }
                assert forall |x| s2_right.contains(x)
                implies ss2.contains(x)
                by {
                    let i = choose|i: int| 0 <= i < s2_right.len() && s2_right[i] === x;
                    assert(s2[i + (pivot_index as int) + 1] === s2_right[i]);
                    assert(s2[i + (pivot_index as int) + 1] === ss2[i + (pivot_index as int) + 1 - start as int]);
                    assert(ss2.contains(x));
                }
                assert forall |x, y| s2_right.contains(x) && s2_right.contains(y)
                implies #[trigger] less.requires((x, y)) by {
                    assert(ss2.contains(x));
                    assert(ss2.contains(y));
                }
            }
            if pivot_index + 1 < end - 1 {
                self.sort(pivot_index + 1, end, less, Ghost(speclt));
            }
            let ghost s3 = self@;
            let ghost ss3 = s3.subrange(start as int, end as int);
            let ghost (s3_left, s3_right) = (
                s3.subrange(start as int, pivot_index as int),
                s3.subrange(pivot_index as int + 1, end as int)
            );
            proof {
                s3.to_multiset_ensures();
                ss3.to_multiset_ensures();
                s3_left.to_multiset_ensures();
                s3_right.to_multiset_ensures();
                // prove multiset
                lemma_multiset_commutative(s3_left.push(s3[pivot_index as int]), s3_right);
                lemma_multiset_commutative(s2_left.push(s2[pivot_index as int]), s2_right);
                lemma_multiset_commutative(s1_left.push(s1[pivot_index as int]), s1_right);
                assert(s3.subrange(start as int, end as int) =~~= s3_left.push(s3[pivot_index as int]) + s3_right);
                assert(s2_left =~~= s3_left);
                assert(s2.subrange(start as int, end as int) =~~= s2_left.push(s1[pivot_index as int]) + s1_right);
                assert(s1_right =~~= s2_right);
                assert(s1.subrange(start as int, end as int) =~~= s1_left.push(s1[pivot_index as int]) + s1_right);
                assert(s3.subrange(start as int, end as int).to_multiset() =~~= s1.subrange(start as int, end as int).to_multiset());
                // prove order
                assert forall |i: int, j: int| start as int <= i < j < end as int
                implies !speclt(#[trigger]self@[j], #[trigger]self@[i])
                by {
                    let v1 = self@[i];
                    let v2 = self@[j];
                    if i <= (pivot_index as int) <= j {
                        if j > pivot_index as int {
                            assert(pivot_index as int + 1 <= j < (end as int));
                            assert(v2 === s3_right[j - 1 - pivot_index as int]);
                            assert(s3_right.contains(v2));
                            assert(s3_right.to_multiset().contains(v2));
                            assert(s2_right.to_multiset().contains(v2));
                            assert(s2_right.contains(v2));
                            assert(s2.contains(v2));
                            let jj = choose |jj| s2[jj] === v2 && ((pivot_index as int) < jj < (end as int));
                            assert(s2[jj] === v2);
                            assert((pivot_index as int) < jj < (end as int));
                            assert(s2[jj] === s1[jj]);
                            assert(!speclt(s1[jj], s1[pivot_index as int]));
                        } else {
                            assert(!speclt(self@[pivot_index as int], v2));
                        }
                        if i != pivot_index as int {
                            assert(s2[i] === v1);
                            assert(s2[i] === s2_left[i - start as int]);
                            assert(s2_left.contains(v1));
                            assert(s2_left.to_multiset().contains(v1));
                            assert(s1_left.to_multiset().contains(v1));
                            assert(s1_left.contains(v1));
                            assert(speclt(v1, self@[pivot_index as int]));
                        }
                        assert(!speclt(v2, v1));
                    }
                }
                let target = self@.subrange(start as int, end as int);
                assert forall |i: int, j: int| 0 <= i < j < target.len()
                implies !speclt(#[trigger]target[j], #[trigger]target[i])
                by {
                    assert(target[i] === self[i + start as int]);
                    assert(target[j] === self[j + start as int]);
                }
                assert(seq_is_sorted(target, speclt));
            }
        }
    }
}
