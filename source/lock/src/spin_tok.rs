//! The ghost state behind [`crate::spin::RawSpinLock`]: who is queued, who is
//! being served, and where the contents are.
//!
//! Kept apart from the running code because it is what the lock's correctness
//! rests on. The tokens it generates are what the two counters are tied to:
//! `current` and `holder` each own one, a thread waiting in the queue owns a
//! `tickets` token for its number, and the thread being served owns the
//! `holding` token that lets it hand the contents back.
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

use crate::pred::LockPredicate;

verus! {

/// The last ticket that can be issued, past which the counter would wrap.
pub open spec fn spec_max_ticket() -> nat {
    u64::MAX as nat
}

} // verus!
// Who is queued, who is being served, and where the contents are.
tokenized_state_machine! {
TicketToks<V, Pred: LockPredicate<V>> {
    fields {
        #[sharding(constant)]
        pub pred: Pred,

        /// The next ticket to hand out.
        #[sharding(variable)]
        pub current: nat,

        /// The ticket being served.
        #[sharding(variable)]
        pub holder: nat,

        /// One token per thread that has taken a ticket and is still waiting.
        #[sharding(map)]
        pub tickets: Map<nat, ()>,

        /// The ticket of the thread that has reached the head of the queue.
        #[sharding(option)]
        pub holding: Option<nat>,

        /// The contents, here whenever nobody is being served.
        #[sharding(storage_option)]
        pub storage: Option<V>,
    }

    #[invariant]
    pub fn queue_ordered(&self) -> bool {
        self.holder <= self.current
    }

    #[invariant]
    pub fn holder_bounded(&self) -> bool {
        self.holder <= spec_max_ticket()
    }

    /// The counters are `u64`s in the running code, so `current` has to stay
    /// where one fits.
    #[invariant]
    pub fn current_bounded(&self) -> bool {
        self.current <= spec_max_ticket()
    }

    #[invariant]
    pub fn tickets_waiting(&self) -> bool {
        forall|k: nat| #[trigger]
            self.tickets.dom().contains(k) ==> self.holder <= k && k < self.current
    }

    #[invariant]
    pub fn holder_is_served(&self) -> bool {
        self.holding is Some ==> {
            &&& self.holding->0 == self.holder
            &&& self.holder < self.current
            &&& !self.tickets.dom().contains(self.holder)
        }
    }

    #[invariant]
    pub fn contents_when_unserved(&self) -> bool {
        &&& (self.storage is Some) == (self.holding is None)
        &&& self.storage is Some ==> self.pred.inv(self.storage->0)
    }

    init!{
        initialize(pred: Pred, v: V) {
            require pred.inv(v);
            init pred = pred;
            init current = 0;
            init holder = 0;
            init tickets = Map::empty();
            init holding = Option::None;
            init storage = Option::Some(v);
        }
    }

    transition!{
        take_ticket() {
            require pre.current < spec_max_ticket();
            update current = (pre.current + 1) as nat;
            add tickets += [ pre.current => () ] by {
                assert(!pre.tickets.dom().contains(pre.current));
            };
        }
    }

    transition!{
        enter(n: nat) {
            require pre.holder == n;
            remove tickets -= [ n => () ];
            add holding += Some(n);
            birds_eye let v = pre.storage->0;
            withdraw storage -= Some(v) by {
                assert(pre.holding is None);
            };
            assert pre.pred.inv(v) by {
                assert(pre.holding is None);
            };
        }
    }

    transition!{
        leave(n: nat, v: V) {
            require pre.pred.inv(v);
            remove holding -= Some(n);
            assert pre.holder == n;
            assert pre.holder < spec_max_ticket();
            update holder = (n + 1) as nat;
            deposit storage += Some(v);
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, pred: Pred, v: V) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            assert(Map::<nat, ()>::empty().dom() =~= Set::<nat>::empty());
        }
    }

    #[inductive(take_ticket)]
    fn take_ticket_inductive(pre: Self, post: Self) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            if k != pre.current {
                assert(pre.tickets.dom().contains(k));
            }
        }
    }

    #[inductive(enter)]
    fn enter_inductive(pre: Self, post: Self, n: nat) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            assert(pre.tickets.dom().contains(k));
        }
    }

    #[inductive(leave)]
    fn leave_inductive(pre: Self, post: Self, n: nat, v: V) {
        assert forall|k: nat| #[trigger] post.tickets.dom().contains(k) implies post.holder <= k
            && k < post.current by {
            assert(pre.tickets.dom().contains(k));
            assert(k != pre.holder);
        }
    }
}
}
