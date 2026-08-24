//! What a lock over tracked state has to promise, whoever wrote it.
//!
//! [`RawSpinLock`](crate::RawSpinLock) is one implementation; an embedder that
//! already has a lock -- because its scheduler needs to know about blocking,
//! because it wants an existing verified lock, or because the hardware offers
//! something better than a ticket -- implements this trait instead and keeps
//! the rest of the verification unchanged.
//!
//! The contract is deliberately small. Nothing here says how exclusion is
//! achieved, only that the contents come out satisfying the predicate and that
//! putting them back takes a [`Hold`](RawLock::Hold), which is what makes a
//! release by a thread that is not holding the lock unprovable.
use vstd::prelude::*;

use crate::pred::LockPredicate;

verus! {

/// A mutual-exclusion lock over tracked state.
///
/// Guards nothing the compiler can see: what goes in and comes out is ghost,
/// which is what a lock over memory owned elsewhere needs. A lock that owns
/// data is this plus a cell, the way [`SpinLock`](crate::SpinLock) is built
/// from [`RawSpinLock`](crate::RawSpinLock).
///
/// There is no `try_lock`. A fair lock cannot offer one without leaving the
/// threads behind the abandoned place waiting for a turn that never comes, and
/// an implementation that can offer one is free to do so on its own type.
pub trait RawLock<V, Pred: LockPredicate<V>>: Sized {
    /// Proof that the caller is the current holder, and the right to release.
    ///
    /// Linear: it is produced by [`acquire`](Self::acquire) and consumed by
    /// [`release`](Self::release), so it cannot be duplicated to release
    /// twice, and dropping it leaves the lock held for ever.
    type Hold;

    /// What distinguishes one lock from another, in the proof.
    ///
    /// Abstract because an implementation without ghost state has no instance
    /// to name; anything that separates locks will do.
    type Id;

    /// Which lock this is, for matching holds against it.
    spec fn id(&self) -> Self::Id;

    /// The predicate this lock's contents satisfy.
    spec fn pred(&self) -> Pred;

    /// The lock a hold was taken from.
    spec fn hold_id(hold: &Self::Hold) -> Self::Id;

    /// Builds a lock, free, holding `v`.
    fn new(v: Tracked<V>, pred: Ghost<Pred>) -> (ret: Self)
        requires
            pred@.inv(v@),
        ensures
            ret.pred() == pred@,
    ;

    /// Takes the lock, waiting for whoever holds it.
    ///
    /// May block for ever: an implementation is not asked to prove that a
    /// waiting thread ever runs, only that the thread that gets in is alone.
    fn acquire(&self) -> (ret: (Tracked<V>, Self::Hold))
        ensures
            self.pred().inv(ret.0@),
            Self::hold_id(&ret.1) == self.id(),
    ;

    /// Gives the contents back and releases the lock.
    ///
    /// Takes the contents rather than trusting the caller to have left them
    /// alone, so whatever is put back has to satisfy the predicate.
    fn release(&self, hold: Self::Hold, v: Tracked<V>)
        requires
            Self::hold_id(&hold) == self.id(),
            self.pred().inv(v@),
    ;
}

} // verus!
