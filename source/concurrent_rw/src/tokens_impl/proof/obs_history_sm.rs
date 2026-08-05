//! **What a reader remembers:** a growing set of values, and duplicable evidence of membership.
//!
//! Built on a tokenized state machine. Its counterpart, [`super::obs_history`], gets the same
//! API from a hand-written resource algebra.
//!
//! Neither can use a ready-made set resource from vstd: they all reject recursive types, and the
//! set here holds snapshots, which are recursive -- a snapshot names a payload, payloads hold
//! readers, readers hold snapshots again.
//!
//! ```text
//!         ObsHistory<A>              Observed<A>
//!         exclusive custody          duplicable
//!         of what has been seen      "A was seen"
//!
//!    observe(v) : requires seen(v)          -> evidence of it
//!    insert(v)  : adds v to the set         -> evidence of it
//!    is_seen()  : evidence + history        ==> the set contains it
//! ```
//!
//! ## Why there is no relation in here
//!
//! An earlier version tracked a `current` value and guaranteed that everything observed reaches
//! it, along a preorder supplied as a trait bound. That cannot work: the element type is a
//! snapshot, so the bound would land on `Reader`, and a payload holds readers -- the trait
//! implementations chase each other in a circle.
//!
//! So this keeps only what needs a resource: monotonicity of the set. The reachability guarantee
//! lives in `ReaderState::inv`, as "everything in the set reaches the pair stored now", where the
//! model's traits are in scope and transitivity can be applied. Nothing is lost -- a set that
//! only grows is what makes such an invariant worth stating.
//!
//! ## Why membership is persistent, not fractional
//!
//! Having seen something is a fact about the past, so there is nothing to police: no exclusivity
//! to protect, no reason to count copies. That makes it `persistent_set`, and it is what keeps
//! this usable at all for a type with no finite enumeration -- the fractional scheme it replaced
//! had to pre-allocate one whole-fraction token per possible value.
use verus_state_machines_macros::*;
use vstd::prelude::*;

tokenized_state_machine!(
    // `accept_recursive_types(A)` because snapshots are recursive; see the module docs.
    #[verifier::accept_recursive_types(A)]
    obs_history<A> {
        fields {
            /// Everything seen so far. Exclusive: only whoever holds custody may add to it.
            #[sharding(variable)]
            pub seen: Set<A>,
            /// The same set, as duplicable evidence. Never shrinks.
            #[sharding(persistent_set)]
            pub observed: Set<A>,
        }

        #[invariant]
        pub fn observed_were_seen(&self) -> bool {
            forall|x: A| #[trigger] self.observed.contains(x) ==> self.seen.contains(x)
        }

        init!{
            start(v: A) {
                init seen = Set::empty().insert(v);
                init observed = Set::empty().insert(v);
            }
        }

        #[inductive(start)]
        fn start_inductive(post: Self, v: A) {
        }

        /// Evidence for something already seen. Free: the element is in the set either way.
        transition!{
            observe(v: A) {
                require pre.seen.contains(v);
                add observed (union)= set { v };
            }
        }

        #[inductive(observe)]
        fn observe_inductive(pre: Self, post: Self, v: A) {
        }

        /// Add something new, and take evidence of it.
        transition!{
            insert(v: A) {
                update seen = pre.seen.insert(v);
                add observed (union)= set { v };
            }
        }

        #[inductive(insert)]
        fn insert_inductive(pre: Self, post: Self, v: A) {
        }

        /// **The point of this module.** Evidence is never stale: what it names is still in the
        /// set, and the set only grows.
        property!{
            is_seen(v: A) {
                have observed >= set { v };
                assert pre.seen.contains(v);
            }
        }
    }
);

verus! {

/// Custody of the set: the right to add to it, and to say what is in it.
///
/// Held by whoever may change the value -- in the reader/writer model, the state living inside
/// the atomic invariant.
pub tracked struct ObsHistory<A> {
    tracked inst: obs_history::Instance<A>,
    tracked seen: obs_history::seen<A>,
}

/// Evidence that `value()` was seen. Duplicable, and never goes stale.
pub tracked struct Observed<A> {
    tracked tok: obs_history::observed<A>,
}

impl<A> ObsHistory<A> {
    /// Identifies which history this is. All pieces of one history share it.
    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    /// Everything seen so far.
    pub closed spec fn seen(self) -> Set<A> {
        self.seen.value()
    }

    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        self.seen.instance_id() == self.inst.id()
    }

    /// A fresh history that has seen `v`, together with evidence of it.
    pub proof fn new(v: A) -> (tracked result: (ObsHistory<A>, Observed<A>))
        ensures
            result.0.seen() == Set::<A>::empty().insert(v),
            result.1.value() == v,
            result.0.id() == result.1.id(),
    {
        let tracked (Tracked(inst), Tracked(seen), Tracked(mut observed)) = obs_history::Instance::<
            A,
        >::start(v);
        let tracked history = ObsHistory { inst, seen };
        let tracked evidence = Observed { tok: observed.remove(v) };
        assert(history.wf());
        (history, evidence)
    }

    /// Evidence for something already in the set.
    pub proof fn observe(tracked &self, v: A) -> (tracked result: Observed<A>)
        requires
            self.seen().contains(v),
        ensures
            result.value() == v,
            result.id() == self.id(),
    {
        use_type_invariant(self);
        let tracked tok = self.inst.observe(v, &self.seen);
        Observed { tok }
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
        let tracked observed = self.inst.insert(v, &mut self.seen);
        Observed { tok: observed }
    }

    /// **The point of this module.** Evidence still names something in the set.
    pub proof fn is_seen(tracked &self, tracked evidence: &Observed<A>)
        requires
            self.id() == evidence.id(),
        ensures
            self.seen().contains(evidence.value()),
    {
        use_type_invariant(self);
        self.inst.is_seen(evidence.value(), &self.seen, &evidence.tok);
    }
}

impl<A> Observed<A> {
    /// Identifies which history this evidence came from.
    pub closed spec fn id(self) -> InstanceId {
        self.tok.instance_id()
    }

    /// What was seen.
    pub closed spec fn value(self) -> A {
        self.tok.element()
    }

    /// Another copy. Free: knowledge about the past is duplicable.
    pub proof fn duplicate(tracked &self) -> (tracked result: Observed<A>)
        ensures
            result.value() == self.value(),
            result.id() == self.id(),
    {
        Observed { tok: self.tok.clone() }
    }
}

} // verus!
