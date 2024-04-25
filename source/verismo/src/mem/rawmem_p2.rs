use super::*;
verus! {

impl RawMemPerms {
    // TODO
    #[verifier(external_body)]
    pub proof fn tracked_split_ranges(tracked &mut self, ranges: Set<(int, nat)>) -> (tracked ret:
        Self) where Self: core::marker::Sized
        requires
            forall|r| ranges.contains(r) && r.1 > 0 ==> old(self).contains_range(r),
            old(self).wf(),
        ensures
            self.wf(),
            ret.wf(),
            forall|r| old(self).contains_range(r) ==> self.contains_except(r, ranges),
            forall|r, snp|
                old(self).contains_snp(r, snp) ==> #[trigger] self.contains_with_snp_except(
                    r,
                    snp,
                    ranges,
                ),
            forall|r| ranges.contains(r) ==> ret.eq_at(*old(self), r),
            forall|r| ranges.contains(r) ==> self.no_range(r),
            forall|r|
                old(self).contains_range(r) && ranges_disjoint(ranges, r) ==> self.eq_at(
                    *old(self),
                    r,
                ),
            forall|r: (int, nat)|
                r.1 > 0 && !old(self).contains_range(r) ==> !self.contains_range(r)
                    && !ret.contains_range(r),
    {
        unimplemented!()
    }
}

} // verus!
