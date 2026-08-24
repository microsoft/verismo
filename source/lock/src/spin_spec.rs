//! What each of the fair spin lock's counters must agree with its ghost token
//! about.
//!
//! Both say the same thing -- the counter in memory and the token in the state
//! machine hold the same number, for the same lock -- and that agreement is
//! what lets a thread reason about [`crate::spin_tok::TicketToks`] from a
//! value it read off an atomic.
use core::marker::PhantomData;

use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

use crate::pred::LockPredicate;
use crate::spin_tok::TicketToks;

verus! {

/// What the `current` counter and its ghost token must jointly satisfy.
pub struct CurrentInv<V, Pred>(PhantomData<(V, Pred)>);

impl<V, Pred: LockPredicate<V>> AtomicInvariantPredicate<
    InstanceId,
    u64,
    TicketToks::current<V, Pred>,
> for CurrentInv<V, Pred> {
    open spec fn atomic_inv(k: InstanceId, u: u64, g: TicketToks::current<V, Pred>) -> bool {
        &&& g.instance_id() == k
        &&& g.value() == u as nat
    }
}

/// What the `holder` counter and its ghost token must jointly satisfy.
pub struct HolderInv<V, Pred>(PhantomData<(V, Pred)>);

impl<V, Pred: LockPredicate<V>> AtomicInvariantPredicate<
    InstanceId,
    u64,
    TicketToks::holder<V, Pred>,
> for HolderInv<V, Pred> {
    open spec fn atomic_inv(k: InstanceId, u: u64, g: TicketToks::holder<V, Pred>) -> bool {
        &&& g.instance_id() == k
        &&& g.value() == u as nat
    }
}

} // verus!
