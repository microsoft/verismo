//! **What a reader remembers:** a growing set of values, and duplicable evidence of membership.
//!
//! Built by hand on vstd's [`Resource`], from a small resource algebra. Its state-machine
//! counterpart gets the same API from a tokenized state machine.
//!
//! The algebra is the usual authority/knowledge split: one authority holds the whole set, and
//! knowledge is a subset anyone may hold a copy of. Validity says knowledge is covered by the
//! authority, which is the whole guarantee -- evidence never names something outside the set.
//!
//! Duplicating evidence needs no rule of its own. Knowledge composes by union, union is
//! idempotent, so `op(f, f) == f` and splitting `f` into `f` and `f` is an ordinary split.
//!
//! ## Recursion
//!
//! The element is a snapshot, which is recursive -- a snapshot names a payload, payloads hold
//! readers, readers hold snapshots again. Nothing here has to claim that is sound.
//! `accept_recursive_types` is needed only for types whose insides the verifier cannot see;
//! `SeenRA` is an ordinary ghost struct, so Verus checks the positivity itself.
//!
//! ## Why the set, and not a relation
//!
//! See the state-machine observation-history implementation: the element is a snapshot, so a
//! `RWShared`, and a payload holds readers. The reachability guarantee lives in `RWState::inv`
//! instead, where the model's traits are in scope.
use vstd::prelude::*;

#[cfg(verus_only)]
use vstd::modes::tracked_swap;
use vstd::resource::algebra::{Resource, ResourceAlgebra};
#[cfg(verus_only)]
use vstd::resource::Loc;

verus! {

/// Authority over a growing set, beside duplicable knowledge of part of it.
///
/// At most one authority may exist. `bad` records that two were composed, which keeps
/// composition total -- it is defined on every pair -- while making the clash invalid.
///
/// Deliberately a plain ghost struct: see the module docs on recursion.
pub ghost struct SeenRA<A> {
    pub auth: Option<Set<A>>,
    pub bad: bool,
    pub frag: Set<A>,
}

impl<A> ResourceAlgebra for SeenRA<A> {
    open spec fn valid(self) -> bool {
        !self.bad && (self.auth is Some ==> self.frag.subset_of(self.auth->Some_0))
    }

    open spec fn op(a: Self, b: Self) -> Self {
        SeenRA {
            auth: if a.auth is None {
                b.auth
            } else if b.auth is None {
                a.auth
            } else {
                Some(a.auth->Some_0.union(b.auth->Some_0))
            },
            bad: a.bad || b.bad || (a.auth is Some && b.auth is Some),
            frag: a.frag.union(b.frag),
        }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        let l = Self::op(a, Self::op(b, c));
        let r = Self::op(Self::op(a, b), c);
        assert(l.frag =~= r.frag);
        if l.auth is Some && r.auth is Some {
            assert(l.auth->Some_0 =~= r.auth->Some_0);
        }
    }

    proof fn commutative(a: Self, b: Self) {
        let l = Self::op(a, b);
        let r = Self::op(b, a);
        assert(l.frag =~= r.frag);
        if l.auth is Some && r.auth is Some {
            assert(l.auth->Some_0 =~= r.auth->Some_0);
        }
    }

    proof fn valid_op(a: Self, b: Self) {
    }
}

/// The authority for a set, holding no knowledge of its own.
spec fn auth_of<A>(s: Set<A>) -> SeenRA<A> {
    SeenRA { auth: Some(s), bad: false, frag: Set::empty() }
}

/// Knowledge of one value, claiming no authority.
spec fn frag_of<A>(v: A) -> SeenRA<A> {
    SeenRA { auth: None, bad: false, frag: Set::empty().insert(v) }
}

/// Custody of the set: the right to add to it, and to say what is in it.
///
/// Held by whoever may change the value -- in the reader/writer model, the state living inside
/// the atomic invariant.
pub tracked struct ObsHistory<A> {
    tracked r: Resource<SeenRA<A>>,
}

/// Evidence that `value()` was seen. Duplicable, and never goes stale.
pub tracked struct Observed<A> {
    ghost v: A,
    tracked r: Resource<SeenRA<A>>,
}

impl<A> ObsHistory<A> {
    /// Identifies which history this is. All pieces of one history share it.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// Everything seen so far.
    pub closed spec fn seen(self) -> Set<A> {
        self.r.value().auth->Some_0
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.r.value() == auth_of::<A>(self.seen())
    }

    /// A fresh history that has seen `v`, together with evidence of it.
    pub proof fn new(v: A) -> (tracked result: (ObsHistory<A>, Observed<A>))
        ensures
            result.0.seen() == Set::<A>::empty().insert(v),
            result.1.value() == v,
            result.0.id() == result.1.id(),
    {
        let ghost s = Set::empty().insert(v);
        let ghost whole = SeenRA { auth: Some(s), bad: false, frag: s };
        assert(whole.valid());
        let tracked r = Resource::alloc(whole);
        assert(whole.frag =~= SeenRA::op(auth_of::<A>(s), frag_of(v)).frag);
        let tracked (a, f) = r.split(auth_of::<A>(s), frag_of(v));
        (ObsHistory { r: a }, Observed { v, r: f })
    }

    /// Evidence for something already in the set. Free: the authority already covers it.
    pub proof fn observe(tracked &self, v: A) -> (tracked result: Observed<A>)
        requires
            self.seen().contains(v),
        ensures
            result.value() == v,
            result.id() == self.id(),
    {
        use_type_invariant(self);
        let tracked f = self.r.duplicate_previous(frag_of(v));
        Observed { v, r: f }
    }

    /// Add something to the set, and take evidence of it.
    pub proof fn insert(tracked &mut self, v: A) -> (tracked result: Observed<A>)
        ensures
            final(self).id() == old(self).id(),
            final(self).seen() == old(self).seen().insert(v),
            result.value() == v,
            result.id() == final(self).id(),
    {
        use_type_invariant(&*self);
        // Updating needs the resource by value, and `extract` would leave `self` unspecified,
        // which its type invariant forbids. So swap in a throwaway and rebuild `self`.
        let tracked mut held = ObsHistory { r: Resource::alloc(auth_of(Set::<A>::empty())) };
        tracked_swap(self, &mut held);
        let ghost s2 = held.seen().insert(v);
        let tracked ObsHistory { r } = held;
        let ghost target = SeenRA { auth: Some(s2), bad: false, frag: Set::empty().insert(v) };
        let tracked r2 = r.update(target);
        assert(target.frag =~= SeenRA::op(auth_of::<A>(s2), frag_of(v)).frag);
        let tracked (a, f) = r2.split(auth_of::<A>(s2), frag_of(v));
        *self = ObsHistory { r: a };
        Observed { v, r: f }
    }

    /// **The point of this module.** Evidence still names something in the set.
    pub proof fn is_seen(tracked &self, tracked evidence: &Observed<A>)
        requires
            self.id() == evidence.id(),
        ensures
            self.seen().contains(evidence.value()),
    {
        use_type_invariant(self);
        use_type_invariant(evidence);
        // Overlap the two rather than compose them: shared resources need not be disjoint, so
        // this stays available through `&self`. Validity of the overlap is what does the work.
        let tracked joined = self.r.join_shared(&evidence.r);
        joined.validate();
        let ghost j = joined.value();
        let ghost a = auth_of::<A>(self.seen());
        let ghost e = frag_of(evidence.value());
        // Each side either is the overlap or sits below it. Where it sits below, the remainder
        // claims no authority -- two authorities would make `j` invalid -- so `j` keeps this
        // authority either way, and keeps the evidence in its knowledge either way.
        if a != j {
            let ghost c = choose|c: SeenRA<A>| SeenRA::op(a, c) == j;
        }
        if e != j {
            let ghost c = choose|c: SeenRA<A>| SeenRA::op(e, c) == j;
        }
        assert(j.frag.contains(evidence.value()));
    }
}

impl<A> Observed<A> {
    /// Identifies which history this evidence came from.
    pub closed spec fn id(self) -> Loc {
        self.r.loc()
    }

    /// What was seen.
    pub closed spec fn value(self) -> A {
        self.v
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.r.value() == frag_of::<A>(self.value())
    }

    /// Another copy. Free: knowledge is idempotent, so `op(f, f) == f`.
    pub proof fn duplicate(tracked &self) -> (tracked result: Observed<A>)
        ensures
            result.value() == self.value(),
            result.id() == self.id(),
    {
        use_type_invariant(self);
        let tracked f = self.r.duplicate_previous(frag_of(self.v));
        Observed { v: self.v, r: f }
    }
}

} // verus!
