use vstd::prelude::*;

use super::*;

verus! {

pub open spec fn range_to_set(first: int, n: nat) -> Set<int> {
    Set::new(|i: int| first <= i < first + (n as int))
}

pub open spec fn range(first: int, end: int) -> (int, nat) {
    if end > first {
        (first, (end - first) as nat)
    } else {
        (first, 0)
    }
}

#[verifier(inline)]
pub open spec fn range2set(range: (int, nat)) -> Set<int> {
    Set::new(|i: int| within_range(i, range))
}

pub trait VRange {
    spec fn to_set(self) -> Set<int> where Self: core::marker::Sized;

    spec fn end(self) -> int where Self: core::marker::Sized;
}

impl VRange for (int, nat) {
    #[verifier(inline)]
    open spec fn to_set(self) -> Set<int> {
        range2set(self)
    }

    #[verifier(inline)]
    open spec fn end(self) -> int {
        self.0 + self.1
    }
}

#[verifier(inline)]
pub open spec fn within_range(x: int, range: (int, nat)) -> bool {
    range.0 <= x < range.0 + range.1
}

#[verifier(inline)]
pub open spec fn inside_range(x: (int, nat), range: (int, nat)) -> bool {
    &&& range.0 <= x.0 < range.0 + range.1
    &&& x.0 + x.1 <= range.0 + range.1
}

pub open spec fn inside_ranges(r2: (int, nat), rs: Set<(int, nat)>) -> bool {
    exists|r1| #[trigger] rs.contains(r1) && inside_range(r2, r1)
}

#[verifier(inline)]
pub open spec fn after_range(x: (int, nat), range: (int, nat)) -> bool {
    &&& x.0 >= range.0 + range.1
}

pub proof fn lemma_to_set(first: int, n: nat) -> (ret: Set<int>)
    ensures
        ret.len() == n,
        ret.finite(),
        ret === range_to_set(first, n),
    decreases n,
{
    let ret = range_to_set(first, n);
    if n == 0 {
        assert forall|v: int| !range_to_set(first, n).contains(v) by {
            assert(!(first < v && v < first));
        }
        assert(range_to_set(first, n) =~= Set::empty());
        //assert(ret=~~=(Set::empty()));
    }
    if n > 0 {
        let prev = lemma_to_set(first, (n - 1) as nat);
        assert(range_to_set(first, n) =~~= (range_to_set(first, (n - 1) as nat).insert(
            first + (n - 1),
        ))) by {
            assert forall|v| range_to_set(first, n).contains(v) implies range_to_set(
                first,
                (n - 1) as nat,
            ).contains(v) || v === (first + (n - 1)) by {
                assert(first <= v < first + n);
                if (first <= v < first + n - 1) {
                    assert(range_to_set(first, (n - 1) as nat).contains(v));
                } else {
                    assert(v == first + n - 1);
                    assert(v == (first + (n - 1)));
                    assert(v == (first + (n - 1)));
                    assert(v === first + (n - 1));
                }
            }
            assert forall|v|
                range_to_set(first, (n - 1) as nat).contains(v) || v === (first + (n
                    - 1)) implies range_to_set(first, n).contains(v) by {}
        }
    }
    ret
}

pub open spec fn range_disjoint(f1: int, n1: nat, f2: int, n2: nat) -> bool {
    ||| n1 == 0
    ||| n2 == 0
    ||| (f1 >= f2 + n2 as int)
    ||| (f2 >= f1 + n1 as int)
}

pub open spec fn range_disjoint_(r1: (int, nat), r2: (int, nat)) -> bool {
    range_disjoint(r1.0, r1.1, r2.0, r2.1)
}

pub open spec fn ranges_disjoint(rs: Set<(int, nat)>, r2: (int, nat)) -> bool {
    forall|r1| #[trigger] rs.contains(r1) ==> range_disjoint_(r1, r2)
}

pub proof fn proof_range_set_disjoint(r1: (int, nat), r2: (int, nat)) -> (ret: bool)
    ensures
        ret === range_disjoint_(r1, r2),
        ret === range2set(r1).disjoint(range2set(r2)),
{
    lemma_range_set_disjoint(r1.0, r1.1, r2.0, r2.1)
}

pub proof fn lemma_ranges_disjoint_insert(r2: (int, nat), range: (int, nat), rs: Set<(int, nat)>)
    requires
        range_disjoint_(r2, range),
    ensures
        ranges_disjoint(rs, r2) == ranges_disjoint(rs.insert(range), r2),
{
    let rs2 = rs.insert(range);
    assert forall|r|
        inside_range(r, r2) && r.1 != 0 && ranges_disjoint(rs, r) implies ranges_disjoint(
        rs2,
        r,
    ) by {
        assert forall|v| rs2.contains(v) implies range_disjoint_(v, r) by {
            if v !== range {
                assert(rs.contains(v));
            } else {
                assert(range_disjoint_(r2, v));
                assert(range_disjoint_(v, r));
            }
        }
    }
    assert forall|r|
        inside_range(r, r2) && r.1 != 0 && ranges_disjoint(
            rs.insert(range),
            r,
        ) implies ranges_disjoint(rs, r) by {
        assert forall|v| rs.contains(v) implies range_disjoint_(v, r) by {
            assert(rs2.contains(v));
        }
    }
}

pub proof fn lemma_range_set_disjoint(f1: int, n1: nat, f2: int, n2: nat) -> (ret: bool)
    ensures
        ret === range_disjoint(f1, n1, f2, n2),
        ret === range_to_set(f1, n1).disjoint(range_to_set(f2, n2)),
{
    let ret = range_disjoint(f1, n1, f2, n2);
    let set1 = lemma_to_set(f1, n1);
    let set2 = lemma_to_set(f2, n2);
    if ret {
        assert forall|a| set1.contains(a) implies !set2.contains(a) by {}
    } else {
        assert(set1.contains(f1)) by {
            assert(f1 <= f1);
            assert(n1 > 0);
            assert(f1 < f1 + n1 as int);
        }
        assert(set2.contains(f2));
        if !set2.contains(f1) {
            assert(set1.contains(f2));
        }
        if !set1.contains(f2) {
            assert(set2.contains(f1));
        }
        assert(!set1.disjoint(set2));
    }
    ret
}

pub proof fn lemma_range_set_low_high(f1: int, n1: nat, n2: nat)
    requires
        n1 <= n2,
    ensures
        range_to_set(f1, n2) =~~= (range_to_set(f1, n1).union(
            range_to_set(f1 + n1 as int, (n2 - n1) as nat),
        )),
        range_to_set(f1, n1) =~~= (range_to_set(f1, n2).difference(
            range_to_set(f1 + n1 as int, (n2 - n1) as nat),
        )),
{
    let s1 = range_to_set(f1, n2);
    let s2 = range_to_set(f1, n1).union(range_to_set(f1 + n1 as int, (n2 - n1) as nat));
    assert forall|i| s1.contains(i) === s2.contains(i) by {}
}

pub proof fn proof_union_auto<int>()
    ensures
        forall|s1: Set<int>, s2: Set<int>, s3: Set<int>|
            s1.union(s2).union(s3) === s1.union(s2.union(s3)),
        forall|s1: Set<int>, s2: Set<int>| s1.union(s2) === s2.union(s1),
        forall|s1: Set<int>, s2: Set<int>| s1.subset_of(#[trigger] s1.union(s2)),
        forall|s1: Set<int>, s2: Set<int>| s2.subset_of(s1) ==> s1.union(s2) === s1,
{
    assert forall|s1: Set<int>, s2: Set<int>, s3: Set<int>|
        s1.union(s2).union(s3) =~~= (s1.union(s2.union(s3))) by {
        assert forall|a|
            s1.union(s2).union(s3).contains(a) === s1.union(s2.union(s3)).contains(a) by {}
    }
    assert forall|s1: Set<int>, s2: Set<int>| s1.union(s2) =~~= (s2.union(s1)) by {
        lemma_union(s1, s2);
    }
    assert forall|s1: Set<int>, s2: Set<int>| s1.subset_of(#[trigger] s1.union(s2)) by {
        lemma_union(s1, s2);
    }
    assert forall|s1: Set<int>, s2: Set<int>| s2.subset_of(s1) implies s1.union(s2) =~~= (s1) by {
        assert forall|a| s1.union(s2).contains(a) === #[trigger] s1.contains(a) by {}
    }
}

} // verus!
