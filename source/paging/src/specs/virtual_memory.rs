use vstd::prelude::*;
use vstd::raw_ptr::MemContents;
use vstd::raw_ptr::PointsTo;
use vstd::invariant::{AtomicInvariant, InvariantPredicate};

use crate::UniqueAddress;

type PhyPointsTo<T> = PointsTo<T>;

verus! {
struct VirtAddrPerm(UniqueAddress);

impl VirtAddrPerm {
    pub uninterp spec fn address_space(&self) -> Loc;

    #[verifier::type_invariant]
    pub open spec fn wf(&self) -> Loc {
        self.0.address_space() == self.address_space()
    }
}

struct PointsToConstant<T> {
    opt_value: Option<MemContents<T>>,
    ptrs: set<*mut T>,
    points_to: Option<PhyPointsTo<T>>,
}

struct PointsToState<T> {
    ptrs: set<*mut T>,
    points_to: Option<PhyPointsTo<T>>,
}

impl InvariantPredicate<PointsToConstant<T>, PointsToState<T>> for PointsToState<T> {
        open spec fn inv(c: PointsToConstant<T>, s: PointsToState<T>) -> bool {
        &&& c.points_to is None ==> s.points_to is Some
        &&& c.ptrs.subset_of(s.ptrs)
        &&& !c.ptrs.is_empty()
    }
}

struct GeneralPointsTo<T> {
    tracked inner: AtomicInvariant<PointsToConstant<T>, PointsToState<T>, PointsToState<T>>,
    tracked points_to: Option<PointsTo<T>>,
}

impl<T> GeneralPointsTo<T> {
    #[verifier::type_invariant]
    pub open spec fn wf(&self) -> Set<*mut T> {
        self.inner.constant() == self.points_to
    }

    #[verifier::inline]
    pub open spec fn opt_value(&self) -> MemContents<T> {
        self@.opt_value
    }
}
}