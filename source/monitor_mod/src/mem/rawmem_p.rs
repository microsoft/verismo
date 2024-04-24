use super::*;
use crate::ptr::SwSnpMemAttr;
use crate::tspec_e::SecSeqByte;

verus! {

pub tracked struct RawMemPerms {
    perms: Map<int, SnpPointsToRaw>,
}

impl RawMemPerms {
    /*
        // BUG: verus does not support
        // private element in broadcast forall even in private proof
        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        proof fn axiom_map_ext_equal_deep(self, other: Self)
        ensures
            #[trigger](self =~~= other) == (self.perms =~~= other.perms)
        {}*/
    pub closed spec fn ext_equal(self, other: Self) -> bool {
        self.perms =~~= other.perms
    }

    pub open spec fn deep_equal(self, other: Self) -> bool {
        forall|r| #[trigger]
            self.contains_range(r) === #[trigger] other.contains_range(r) && self[r] === other[r]
    }

    pub closed spec fn wf(self) -> bool {
        &&& forall|k: int|
            self.perms.contains_key(k) ==> (#[trigger] self.perms[k])@.range() === (k, 1)
        &&& forall|k: int| self.perms.contains_key(k) ==> (#[trigger] self.perms[k])@.snp.wf()
    }

    pub closed spec fn new(perms: Map<int, SnpPointsToRaw>) -> Self {
        Self { perms }
    }

    pub proof fn tracked_empty() -> (tracked ret: Self)
        ensures
            forall|r| !ret.contains_range(r),
    {
        let tracked ret = Self { perms: Map::tracked_empty() };
        assert forall|r| !ret.contains_range(r) by {
            if r.1 != 0 {
                assert(!ret.perms.contains_key(r.0));
            }
        }
        ret
    }

    pub closed spec fn spec_index(self, range: (int, nat)) -> SnpPointsToBytes {
        let (start, size) = range;
        let s = range2set(range);
        let p = self.perms;
        SnpPointsToBytes {
            pptr: start,
            snp_bytes: Seq::new(size, |i| p[start + i]@.snp_bytes[0]),
            snp: p[start]@.snp,
        }
    }

    // The range should be at least with size 1.
    pub closed spec fn contains_range(self, range: (int, nat)) -> bool {
        //&&& forall |i: int|  within_range(i, range) ==> #[trigger]self.perms.contains_key(i)
        let s = range2set(range);
        let perms = self.perms;
        &&& range.1 > 0
        &&& s.subset_of(perms.dom())
        &&& forall|i: int|
            within_range(i, range) ==> (#[trigger] perms[i])@.snp() === perms[range.0]@.snp()
    }

    pub open spec fn contains_except(&self, range: (int, nat), ranges: Set<(int, nat)>) -> bool {
        forall|r: (int, nat)|
            inside_range(r, range) && ranges_disjoint(ranges, r) && r.1 != 0
                ==> #[trigger] self.contains_range(r)
    }

    pub open spec fn contains_with_snp_except(
        &self,
        range: (int, nat),
        snp: SwSnpMemAttr,
        ranges: Set<(int, nat)>,
    ) -> bool {
        forall|r: (int, nat)|
            (inside_range(r, range) && ranges_disjoint(ranges, r) && r.1 != 0) ==> (
            #[trigger] self.contains_range(r) && self[r].snp() === snp)
    }

    #[verifier(inline)]
    pub open spec fn contains_default_except(
        &self,
        range: (int, nat),
        ranges: Set<(int, nat)>,
    ) -> bool {
        self.contains_with_snp_except(range, SwSnpMemAttr::spec_default(), ranges)
    }

    #[verifier(inline)]
    pub open spec fn contains_init_except(
        &self,
        range: (int, nat),
        ranges: Set<(int, nat)>,
    ) -> bool {
        self.contains_with_snp_except(range, SwSnpMemAttr::init(), ranges)
    }

    #[verifier(inline)]
    pub open spec fn contains_snp(&self, r: (int, nat), snp: SwSnpMemAttr) -> bool {
        &&& self.contains_range(r)
        &&& (self[r]).snp() === snp
    }

    #[verifier(inline)]
    pub open spec fn contains_init_mem(&self, r: (int, nat)) -> bool {
        self.contains_snp(r, SwSnpMemAttr::init())
    }

    #[verifier(inline)]
    pub open spec fn contains_default_mem(&self, r: (int, nat)) -> bool {
        self.contains_snp(r, SwSnpMemAttr::spec_default())
    }

    pub open spec fn contains_default_ranges(&self, ranges: Set<(int, nat)>) -> bool {
        // contains all memory permission validated
        &&& forall|r|
            (ranges.contains(r) && r.1 > 0) ==> #[trigger] self.contains_range(r)
                && self.contains_default_mem(r)
    }

    pub open spec fn no_range(self, range: (int, nat)) -> bool {
        &&& !self.contains_range(range)
        &&& forall|r: (int, nat)| inside_range(r, range) ==> !self.contains_range(r)
    }

    pub closed spec fn dom(self) -> Set<int> {
        self.perms.dom()
    }

    pub closed spec fn remove_range(self, range: (int, nat)) -> Self {
        Self { perms: self.perms.remove_keys(range2set(range)) }
    }

    pub closed spec fn restrict(self, range: (int, nat)) -> Self {
        Self { perms: self.perms.restrict(range.to_set()) }
    }

    pub closed spec fn union(self, other: Self) -> Self {
        Self { perms: self.perms.union_prefer_right(other.perms) }
    }

    #[verifier(inline)]
    pub open spec fn eq_at(self, other: Self, r: (int, nat)) -> bool {
        &&& self.contains_range(r) == other.contains_range(r)
        &&& self.contains_range(r) ==> { self[r] === other[r] }
    }
}

impl RawMemPerms {
    proof fn lemma_restricted_ensures(self, r: (int, nat))
        requires
            r.1 > 0,
        ensures
            forall|r2| inside_range(r2, r) ==> self.eq_at(self.restrict(r), r2),
    {
        assert forall|r2| inside_range(r2, r) implies self.eq_at(self.restrict(r), r2) by {
            self.lemma_restricted(r, r2);
        }
    }

    proof fn lemma_restricted(self, r: (int, nat), r2: (int, nat))
        requires
            r.1 > 0,
            inside_range(r2, r),
        ensures
            self.eq_at(self.restrict(r), r2),
    {
        let restrict = self.restrict(r);
        let perms = restrict.perms;
        let s = r.to_set();
        //assert(perms =~~= self.perms.restrict(r.to_set()));
        assert(s.subset_of(perms.dom()) === s.subset_of(self.perms.dom()));
        assert forall|i: int| within_range(i, r2) implies perms.contains_key(i)
            == self.perms.contains_key(i) && (perms.contains_key(i) ==> (#[trigger] perms[i])
            === self.perms[i]) by {
            assert(r.to_set().contains(i));
            assert(r2.to_set().contains(i));
        }
        if self.contains_range(r2) {
            assert forall|i: int| within_range(i, r2) implies perms.contains_key(i) && (
            perms[i])@.snp() === perms[r2.0]@.snp() by {
                assert(self.perms.contains_key(i));
                assert(self.perms[i]@.snp() === self.perms[r2.0]@.snp());
            }
            assert(perms[r2.0] === self.perms[r2.0]);
            assert(self[r2].bytes() =~~= restrict[r2].bytes());
            assert(self.restrict(r).contains_range(r2));
        }
        if restrict.contains_range(r2) {
            assert forall|i: int| within_range(i, r2) implies (#[trigger] self.perms[i])@.snp()
                === self.perms[r2.0]@.snp() by {
                assert(perms.contains_key(i));
                assert(perms[i]@.snp() === perms[r2.0]@.snp());
            }
            assert(range2set(r2).subset_of(self.perms.dom()));
            assert(self.contains_range(r2));
        }
        assert(self.contains_range(r2) == self.restrict(r).contains_range(r2));
    }

    proof fn lemma_remove_range_not_contains(self, r1: (int, nat), r2: (int, nat))
        requires
            !self.contains_range(r2),
        ensures
            !self.remove_range(r1).contains_range(r2),
    {
        let s2 = r2.to_set();
        let ret = self.remove_range(r1);
        if r2.1 > 0 {
            ret.lemma_restricted(r2, r2);
            self.lemma_restricted(r2, r2);
        }
        if ret.contains_range(r2) {
            assert(self.contains_range(r2)) by {
                assert forall|i: int| range2set(r2).contains(i) implies self.perms.dom().contains(
                    i,
                ) by {
                    assert(ret.perms.contains_key(i));
                    assert(within_range(i, r2));
                }
                assert(range2set(r2).subset_of(self.perms.dom()));
                assert forall|i: int| within_range(i, r2) implies (#[trigger] self.perms[i])@.snp()
                    === self.perms[r2.0]@.snp() by {
                    assert(ret.perms[i]@.snp() === ret.perms[r2.0]@.snp());
                }
            }
        }
    }

    proof fn lemma_remove_range_contains(self, r1: (int, nat), r2: (int, nat))
        requires
            range_disjoint_(r1, r2),
            self.contains_range(r2),
            //self.contains_range(r1),
            r2.1 > 0,
        ensures
            self.remove_range(r1).contains_range(r2),
            self.remove_range(r1)[r2] === self[r2],
    {
        let ret = self.remove_range(r1);
        ret.lemma_restricted(r2, r2);
        self.lemma_restricted(r2, r2);
        proof_range_set_disjoint(r1, r2);
        assert(range2set(r1).disjoint(range2set(r2)));
        assert(self.perms.remove_keys(range2set(r1)).restrict(range2set(r2))
            =~~= self.perms.restrict(range2set(r2)));
        let s2 = range2set(r2);
        assert(s2.contains(r2.0));
        assert(ret.perms.restrict(s2) =~~= self.perms.restrict(s2));
        assert(ret.perms[r2.0] === self.perms[r2.0]);
        assert(ret[r2].snp === self[r2].snp);
        assert(ret[r2].snp_bytes =~~= self[r2].snp_bytes);
    }

    pub proof fn lemma_remove_range_ensures(self, r1: (int, nat), r2: (int, nat)) -> (ret: Self)
        ensures
            ret === self.remove_range(r1),
            inside_range(r2, r1) ==> !ret.contains_range(r2),
            range_disjoint_(r1, r2) && self.contains_range(r2) ==> ret.contains_range(r2) && ret[r2]
                === self[r2],
            !self.contains_range(r2) ==> !ret.contains_range(r2),
    {
        let ret = self.remove_range(r1);
        if r2.1 > 0 {
            if range_disjoint_(r1, r2) && self.contains_range(r2) {
                self.lemma_remove_range_contains(r1, r2);
            }
            if !self.contains_range(r2) {
                self.lemma_remove_range_not_contains(r1, r2);
            }
            if inside_range(r2, r1) {
                assert(!ret.perms.contains_key(r2.0));
            }
        }
        ret
    }

    spec fn ext_eq_contains_except(self, ret: Self, r2: (int, nat), rs: Set<(int, nat)>) -> bool {
        forall|r|
            inside_range(r, r2) && r.1 != 0 && ranges_disjoint(rs, r) ==> (
            #[trigger] self.contains_range(r) == #[trigger] ret.contains_range(r)) && (
            self.contains_range(r) ==> self[r] === ret[r])
    }

    proof fn lemma_except_contains_eq(
        self,
        ret: Self,
        r2: (int, nat),
        snp: SwSnpMemAttr,
        rs: Set<(int, nat)>,
    )
        requires
            self.ext_eq_contains_except(ret, r2, rs),
        ensures
            self.contains_with_snp_except(r2, snp, rs) == ret.contains_with_snp_except(r2, snp, rs),
    {
        if self.contains_with_snp_except(r2, snp, rs) {
            assert forall|r|
                inside_range(r, r2) && r.1 != 0 && ranges_disjoint(
                    rs,
                    r,
                ) implies ret.contains_range(r) && ret[r].snp() === snp by {
                assert(self.contains_range(r));
                assert(ret.contains_range(r));
                assert(self[r] === ret[r]);
            }
            assert(ret.contains_with_snp_except(r2, snp, rs));
        }
        if ret.contains_with_snp_except(r2, snp, rs) {
            assert forall|r|
                inside_range(r, r2) && r.1 != 0 && ranges_disjoint(
                    rs,
                    r,
                ) implies self.contains_range(r) && self[r].snp() === snp by {
                assert(ret.contains_range(r));
                assert(self.contains_range(r));
                assert(self[r] === ret[r]);
            }
            assert(self.contains_with_snp_except(r2, snp, rs));
        }
    }

    pub proof fn proof_remove_range_ensures_except(self, range: (int, nat)) -> (ret: Self)
        ensures
            ret === self.remove_range(range),
            forall|snp, r2, rs|
                range_disjoint_(r2, range) ==> (#[trigger] self.contains_with_snp_except(
                    r2,
                    snp,
                    rs,
                ) == #[trigger] ret.contains_with_snp_except(r2, snp, rs.insert(range))),
            forall|snp, r2, rs|
                range_disjoint_(r2, range) ==> (self.contains_with_snp_except(r2, snp, rs)
                    == ret.contains_with_snp_except(r2, snp, rs)),
            forall|snp, r2, rs|
                inside_range(r2, range) ==> (self.contains_with_snp_except(r2, snp, rs)
                    == self.restrict(range).contains_with_snp_except(r2, snp, rs)),
    {
        let ret = self.remove_range(range);
        assert forall|snp, r2, rs| range_disjoint_(r2, range) implies (
        self.contains_with_snp_except(r2, snp, rs) == ret.contains_with_snp_except(
            r2,
            snp,
            rs,
        )) by {
            assert forall|r| inside_range(r, r2) && r.1 != 0 && ranges_disjoint(rs, r) implies (
            #[trigger] self.contains_range(r) == #[trigger] ret.contains_range(r)) && (
            self.contains_range(r) ==> self[r] === ret[r]) by {
                self.proof_remove_range_ensures(range);
            }
            self.lemma_except_contains_eq(ret, r2, snp, rs);
        }
        assert forall|snp, r2, rs| inside_range(r2, range) implies (self.contains_with_snp_except(
            r2,
            snp,
            rs,
        ) == self.restrict(range).contains_with_snp_except(r2, snp, rs)) by {
            assert forall|r| inside_range(r, r2) && r.1 != 0 && ranges_disjoint(rs, r) implies (
            #[trigger] self.contains_range(r) == #[trigger] self.restrict(range).contains_range(r))
                && (self.contains_range(r) ==> self[r] === self.restrict(range)[r]) by {
                self.proof_remove_range_ensures(range);
            }
            self.lemma_except_contains_eq(self.restrict(range), r2, snp, rs);
        }
        assert forall|snp, r2, rs| range_disjoint_(r2, range) implies (
        #[trigger] self.contains_with_snp_except(r2, snp, rs)
            == #[trigger] ret.contains_with_snp_except(r2, snp, rs.insert(range))) by {
            assert forall|r| inside_range(r, r2) && r.1 != 0 implies ranges_disjoint(rs, r)
                == ranges_disjoint(rs.insert(range), r) by {
                lemma_ranges_disjoint_insert(r, range, rs);
            }
        }
        ret
    }

    pub proof fn proof_remove_range_ensures(self, range: (int, nat)) -> (ret: Self)
        ensures
            ret === self.remove_range(range),
            ret.no_range(range),
            //self.remove_range(range).union(self.restrict(range)) === self,
            forall|r: (int, nat)| range_disjoint_(range, r) ==> self.eq_at(ret, r),
            forall|r: (int, nat)| r.1 > 0 && !self.contains_range(r) ==> !ret.contains_range(r),
            range.1 > 0 ==> forall|r2|
                inside_range(r2, range) ==> self.eq_at(
                    self.restrict(range),
                    r2,
                ),
    //forall |snp, r2, rs| range_disjoint_(r2, range) ==>
    //(self.contains_with_snp_except(r2, snp, rs) == ret.contains_with_snp_except(r2, snp, rs)),
    //forall |snp, r2, rs| inside_range(r2, range) ==>
    //(self.contains_with_snp_except(r2, snp, rs) == self.restrict(range).contains_with_snp_except(r2, snp, rs))

    {
        let ret = self.remove_range(range);
        assert(self.remove_range(range).union(self.restrict(range)).perms =~~= self.perms);
        assert forall|r: (int, nat)|
            r.1 > 0 && range_disjoint_(range, r) && self.contains_range(
                r,
            ) implies ret.contains_range(r) && ret[r] === self[r] by {
            self.lemma_remove_range_ensures(range, r);
        }
        assert forall|r: (int, nat)| r.1 > 0 && !self.contains_range(r) implies !ret.contains_range(
            r,
        ) by {
            self.lemma_remove_range_ensures(range, r);
        }
        assert forall|r: (int, nat)| inside_range(r, range) implies !#[trigger] ret.contains_range(
            r,
        ) by {
            self.lemma_remove_range_ensures(range, r);
        }
        if range.1 > 0 {
            self.lemma_restricted_ensures(range);
        }
        ret
    }

    pub proof fn lemma_contain_range_empty(self)
        ensures
            forall|r: (int, nat)| r.1 == 0 ==> !#[trigger] self.contains_range(r),
    {
    }

    pub proof fn lemma_contain_range_sub(self, r1: (int, nat), r2: (int, nat))
        requires
            self.contains_range(r2),
            inside_range(r1, r2),
            r1.1 > 0,
        ensures
            self.contains_range(r1),
            self[r1].snp() === self[r2].snp(),
    {
        assert forall|i: int| within_range(i, r1) implies #[trigger] self.perms.contains_key(i)
            && self.perms[i]@.snp() === self.perms[r1.0]@.snp() by {
            assert(within_range(i, r2));
            assert(self.perms.contains_key(i));
            assert(self.perms.contains_key(r1.0));
        }
    }

    pub proof fn lemma_contain_except_range_sub(
        self,
        r1: (int, nat),
        r2: (int, nat),
        rs: Set<(int, nat)>,
    )
        requires
            self.contains_except(r2, rs),
            inside_range(r1, r2),
        ensures
            self.contains_except(r1, rs),
    {
        assert forall|r|
            inside_range(r, r1) && r.1 != 0 && ranges_disjoint(
                rs,
                r,
            ) implies #[trigger] self.contains_range(r) by {
            assert(inside_range(r, r2));
            assert(self.contains_except(r2, rs));
            assert(self.contains_range(r));
        }
    }

    pub proof fn lemma_with_except_sub(
        self,
        r1: (int, nat),
        r2: (int, nat),
        snp: SwSnpMemAttr,
        rs: Set<(int, nat)>,
    )
        requires
            self.contains_with_snp_except(r2, snp, rs),
            inside_range(r1, r2) || r1.1 == 0,
        ensures
            self.contains_with_snp_except(r1, snp, rs),
    {
        assert forall|r|
            inside_range(r, r1) && r.1 != 0 && ranges_disjoint(rs, r) implies self.contains_range(r)
            && self.contains_snp(r, snp) by {
            assert(inside_range(r, r2));
            assert(self.contains_range(r));
        }
    }

    pub proof fn proof_contains_range_to_except(self, r1: (int, nat), rs: Set<(int, nat)>)
        requires
            self.contains_range(r1) || r1.1 == 0,
        ensures
            self.contains_except(r1, rs),
            self.contains_with_snp_except(r1, self[r1].snp(), rs),
    {
        let snp = self[r1].snp();
        assert forall|r|
            inside_range(r, r1) && r.1 != 0 && ranges_disjoint(rs, r) implies self.contains_snp(
            r,
            snp,
        ) by {
            assert(inside_range(r, r1));
            assert(self.contains_snp(r1, snp));
            self.lemma_contain_range_sub(r, r1);
        }
    }

    pub proof fn lemma_empty_contains_except(
        self,
        r1: (int, nat),
        snp: SwSnpMemAttr,
        rs: Set<(int, nat)>,
    )
        requires
            inside_ranges(r1, rs) || r1.1 == 0,
        ensures
            self.contains_with_snp_except(r1, snp, rs),
    {
        assert forall|r|
            inside_range(r, r1) && r.1 != 0 && ranges_disjoint(rs, r) implies self.contains_range(r)
            && self.contains_snp(r, snp) by {
            assert(inside_ranges(r1, rs));
            let rr = choose|rr| rs.contains(rr) && inside_range(r1, rr);
            assert(rs.contains(rr));
            assert(inside_range(r1, rr));
            assert(ranges_disjoint(rs, r));
            assert(range_disjoint_(rr, r));
            assert(r1.1 == 0 || rr.1 == 0);
        }
    }

    proof fn _lemma_contain_range_union(self, r1: (int, nat), r2: (int, nat)) -> (r3: (int, nat))
        requires
            self.contains_range(r2),
            self.contains_range(r1),
            self[r2].snp() === self[r1].snp(),
            r1.0 <= r2.0,
            r1.0 + r1.1 >= r2.0,  // r1 and r2 overlaps
            r2.0 + r2.1 >= r1.0 + r1.1,
        ensures
            r3.0 == r1.0,
            r3.0 + r3.1 == r2.0 + r2.1,
            self.contains_range((r3)),
            self[r3].snp() === self[r1].snp(),
    {
        let lower = r1.0;
        let upper = r2.0 + r2.1;
        assert(lower <= upper);
        let ret = (lower, (upper - lower) as nat);
        assert forall|i: int| within_range(i, ret) implies self.perms.contains_key(i) && (
        #[trigger] self.perms[i])@.snp() === self[ret].snp() by {
            assert(r1.0 + r1.1 >= r2.0);
            if (within_range(i, r1)) {
                assert(self.perms.contains_key(i));
                assert(self.perms[i]@.snp() === self[r1].snp());
            } else {
                assert(within_range(i, r2));
                assert(self.perms.contains_key(i));
                assert(self.perms[i]@.snp() === self[r2].snp());
            }
        }
        ret
    }

    pub proof fn lemma_with_except_union(
        self,
        r1: (int, nat),
        r2: (int, nat),
        snp: SwSnpMemAttr,
        rs: Set<(int, nat)>,
    ) -> (r3: (int, nat))
        requires
            self.contains_with_snp_except(r1, snp, rs) || r1.1 == 0,
            self.contains_with_snp_except(r2, snp, rs) || r2.1 == 0,
            r1.0 <= r2.0,
            r1.end() >= r2.0,  // r1 and r2 overlaps
            r2.end() >= r1.0 + r1.1,
        ensures
            r3.0 == r1.0,
            r3.0 + r3.1 == r2.0 + r2.1,
            self.contains_with_snp_except(r3, snp, rs) || r3.1 == 0,
    {
        let lower = r1.0;
        let upper = r2.0 + r2.1;
        assert(lower <= upper);
        let ret = range(lower, upper);
        assert forall|r|
            inside_range(r, ret) && r.1 != 0 && ranges_disjoint(rs, r) implies self.contains_range(
            r,
        ) && self.contains_snp(r, snp) by {
            assert forall|i: int| within_range(i, r) implies self.perms.contains_key(i) && (
            #[trigger] self.perms[i])@.snp() === snp by {
                assert forall|rr| rs.contains(rr) implies range_disjoint_(rr, (i, 1)) by {}
                assert(ranges_disjoint(rs, (i, 1)));
                if (within_range(i, r1)) {
                    assert(r1.1 != 0);
                    assert(inside_range((i, 1), r1));
                    assert(self.contains_range((i, 1)));
                    assert(self.perms.contains_key(i));
                    assert(self.perms[i]@.snp() === snp);
                } else {
                    assert(r2.1 != 0);
                    assert(within_range(i, r2));
                    assert(inside_range((i, 1), r2));
                    assert(self.contains_range((i, 1)));
                    assert(self.perms.contains_key(i));
                    assert(self.perms[i]@.snp() === snp);
                }
            }
            assert(range2set(r).subset_of(self.perms.dom())) by {
                assert forall|i| within_range(i, r) implies self.perms.contains_key(i) by {
                    assert(self.perms[i]@.snp() === snp);
                }
            }
            assert(self.contains_range(r));
        }
        ret
    }

    pub proof fn lemma_contain_range_union(self, r1: (int, nat), r2: (int, nat)) -> (r3: (int, nat))
        requires
            self.contains_range(r2) || r2.1 == 0,
            self.contains_range(r1) || r1.1 == 0,
            self[r2].snp() === self[r1].snp() || r2.1 == 0 || r1.1 == 0,
            r1.0 <= r2.0,
            r1.0 + r1.1 >= r2.0,  // r1 and r2 overlaps
            r2.0 + r2.1 >= r1.0 + r1.1,
        ensures
            r3.0 == r1.0,
            r3.0 + r3.1 == r2.0 + r2.1,
            self.contains_range((r3)) || r3.1 == 0,
            self[r3].snp() === self[r1].snp(),
    {
        let lower = r1.0;
        let upper = r2.0 + r2.1;
        assert(lower <= upper);
        let ret = range(lower, upper);
        if r1.1 > 0 && r2.1 > 0 {
            self._lemma_contain_range_union(r1, r2);
        } else if r1.1 > 0 {
            assert(ret === r1);
        } else {
            assert(ret === r2);
        }
        ret
    }

    proof fn _tracked_insert(tracked &mut self, range: (int, nat), tracked perm: SnpPointsToRaw)
        requires
            old(self).no_range(range),
            old(self).wf(),
            perm@.range() === range,
            perm@.snp.wf(),
            range.1 > 0,
        ensures
            self.wf(),
            self[range].sw_eq(perm@),
            self.contains_range(range),
            *old(self) === self.remove_range(range),
            self.ext_equal((*old(self)).union(self.restrict(range))),
        decreases range.1,
    {
        let oldself = *self;
        let (start, size) = range;
        let last = start + size - 1;
        if size > 1 {
            let prev_range = (start, (size - 1) as nat);
            let tracked (prev_perm, p) = perm.trusted_split((size - 1) as nat);
            self._tracked_insert(prev_range, prev_perm);
            let prevself = *self;
            self.perms.tracked_insert(last, p);
            assert(prev_range.to_set().insert(last) =~~= range.to_set());
            assert(oldself.perms =~~= self.remove_range(range).perms) by {
                prevself.lemma_remove_range_ensures(prev_range, (last, 1));
                assert(!prevself.contains_range((last, 1)));
                assert(!prevself.perms.contains_key(last));
                assert(self.perms.remove(last) =~~= prevself.perms);
                assert(oldself.perms =~~= prevself.remove_range(prev_range).perms);
            }
            assert(self[range].sw_eq(perm@)) by {
                assert(self[range].bytes() =~~= prevself[prev_range].bytes() + p@.bytes());
            }
        } else if size == 1 {
            self.perms.tracked_insert(last, perm);
            assert(self[range].sw_eq(perm@));
            assert(oldself.perms =~~= self.remove_range(range).perms) by {
                assert(!oldself.contains_range((last, 1)));
                //assert(!oldself.perms.contains_key(last));
            }
        }
    }

    pub proof fn tracked_insert(tracked &mut self, range: (int, nat), tracked perm: SnpPointsToRaw)
        requires
            forall|r| inside_range(r, range) ==> !old(self).contains_range(r),
            old(self).wf(),
            perm@.range() === range,
            perm@.snp.wf(),
            range.1 > 0,
        ensures
            self.wf(),
            self[range].sw_eq(perm@),
            self.contains_range(range),
            *old(self) === self.remove_range(
                range,
            ),
    //forall |r: (int, nat)| r.1 > 0 && range_disjoint_(range, r) && self.contains_range(r) ==> old(self).contains_range(r) && old(self)[r] === self[r],
    //forall |r: (int, nat)| r.1 > 0 && !self.contains_range(r) ==> !old(self).contains_range(r)

    {
        let ret = self._tracked_insert(range, perm);
        self.proof_remove_range_ensures(range);
        ret
    }

    proof fn _tracked_remove(tracked &mut self, range: (int, nat)) -> (tracked ret: SnpPointsToRaw)
        requires
            old(self).contains_range(range),
            range.1 > 0,
            old(self).wf(),
        ensures
            ret@.range() === range,
            ret@.sw_eq(old(self)[range]),
            ret@.snp.wf(),
            self.wf(),
            forall|i|
                (!(range.0 <= i < range.0 + range.1) && old(self).perms.contains_key(i))
                    ==> self.perms.contains_key(i),
            forall|i| (range.0 <= i < range.0 + range.1) ==> !self.perms.contains_key(i),
            forall|i|
                !(range.0 <= i < range.0 + range.1) && old(self).perms.contains_key(i)
                    ==> #[trigger] self.perms[i] === old(self).perms[i],
        decreases range.1,
    {
        let (start, size) = range;
        if size > 1 {
            let prev_range = (start, (size - 1) as nat);
            let tracked prev = self._tracked_remove(prev_range);
            let last = start + size - 1;
            //assert(self.perms[last] === old(self).perms[last]);
            let tracked last_bytes = self.perms.tracked_remove(last);
            assert(last_bytes@.snp() === old(self).perms[start]@.snp());
            prev.trusted_join(last_bytes)
        } else {
            self.perms.tracked_remove(start)
        }
    }

    pub proof fn tracked_remove(tracked &mut self, range: (int, nat)) -> (tracked ret:
        SnpPointsToRaw)
        requires
            old(self).contains_range(range),
            range.1 > 0,
            old(self).wf(),
        ensures
            ret@.range() === range,
            ret@.sw_eq(old(self)[range]),
            ret@.snp.wf(),
            self.wf(),
            *self === old(self).remove_range(
                range,
            ),
    //self.no_range(range),
    //forall |r: (int, nat)| inside_range(r, range) ==> !self.contains_range(r),
    //forall |r: (int, nat)| (r.1 > 0 && range_disjoint_(range, r) && old(self).contains_range(r)) ==> self.contains_range(r) && self[r] === old(self)[r],
    //forall |r: (int, nat)| (r.1 > 0 && !old(self).contains_range(r)) ==> !self.contains_range(r)

    {
        self.proof_remove_range_ensures(range);
        let tracked removed = self.perms.tracked_remove_keys(range2set(range));
        let tracked mut removed = RawMemPerms { perms: removed };
        removed._tracked_remove(range)
    }

    pub proof fn tracked_split(tracked &mut self, range: (int, nat)) -> (tracked ret: Self)
        requires
            range.1 > 0,
            old(self).wf(),
        ensures
            ret.wf(),
            self.wf(),
            ret === old(self).restrict(range),
            *self === old(self).remove_range(range),
            self.no_range(range),
    {
        self.proof_remove_range_ensures(range);
        let dom = self.perms.dom();
        let s = range2set(range);
        let toremove = s.intersect(self.perms.dom());
        assert(s.intersect(dom).intersect(dom) =~~= s.intersect(dom));
        assert(self.restrict(range).perms =~~= self.perms.restrict(s.intersect(self.perms.dom())));
        assert(self.perms.remove_keys(s) =~~= self.perms.remove_keys(
            s.intersect(self.perms.dom()),
        ));
        let tracked removed = self.perms.tracked_remove_keys(toremove);
        RawMemPerms { perms: removed }
    }

    pub proof fn tracked_union(tracked &mut self, tracked other: Self) where
        Self: core::marker::Sized,

        requires
            old(self).wf(),
            other.wf(),
        ensures
            *self === (*old(self)).union(other),
            self.wf(),
    {
        self.perms.tracked_union_prefer_right(other.perms);
    }

    #[verifier(external_body)]
    pub proof fn lemma_union_propograte_except(
        mem1: Self,
        mem2: Self,
        range: (int, nat),
        snp: SwSnpMemAttr,
        except1: Set<(int, nat)>,
        except2: Set<(int, nat)>,
    )
        requires
            mem1.contains_with_snp_except(range, snp, except1),
            forall|r| except1.contains(r) ==> mem2.contains_with_snp_except(r, snp, except2),
        ensures
            mem1.union(mem2).contains_with_snp_except(range, snp, except2),
    {
    }
}

} // verus!
