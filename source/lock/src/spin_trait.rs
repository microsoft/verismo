//! What a mutual-exclusion lock over data has to promise, whoever wrote it.
//!
//! [`SpinLock`](crate::SpinLock) is one implementation; an embedder that
//! already has a lock -- because its scheduler needs to know about blocking,
//! because it wants a lock it has already verified, or because the hardware
//! offers something better than a ticket -- implements this trait instead and
//! keeps the rest of its verification unchanged.
use core::ops::{Deref, DerefMut};

use vstd::prelude::*;

use crate::pred::LockPredicate;

verus! {

/// A lock that owns its data, in the shape of `std::sync::Mutex`.
///
/// The contract is deliberately small. Nothing here says how exclusion is
/// achieved, only that a guard exists at most once at a time and that the data
/// satisfies the predicate whenever no one holds it.
///
/// There is no `try_lock`. A fair lock cannot offer one without leaving the
/// threads behind the abandoned place waiting for a turn that never comes, and
/// an implementation that can offer one is free to do so on its own type.
///
/// The lifetime is on the trait rather than on `Guard`, because Verus does
/// not support generic associated types. A caller generic over the lock
/// therefore writes `L: for<'a> SpinLockTrait<'a, T, Pred>`.
pub trait SpinLockTrait<'a, T, Pred: LockPredicate<T>>: Sized + 'a {
    /// Proof that the caller holds the lock, and the way to the data.
    ///
    /// Linear: produced by [`lock`](Self::lock) and consumed by
    /// [`unlock`](Self::unlock), so it cannot be duplicated to release twice,
    /// and dropping it leaves the lock held for ever.
    type Guard: Deref<Target = T> + DerefMut;

    /// What is true of the data whenever no one holds the lock.
    spec fn inv(&self, v: T) -> bool;

    /// The data a guard is holding.
    spec fn guard_view(guard: &Self::Guard) -> T;

    /// The lock a guard was taken from.
    spec fn guard_lock(guard: &Self::Guard) -> &'a Self;

    /// Builds a lock owning `v`.
    fn new(v: T, pred: Ghost<Pred>) -> (ret: Self)
        requires
            pred@.inv(v),
        ensures
            forall|w: T| #[trigger] ret.inv(w) == pred@.inv(w),
    ;

    /// Takes the lock, waiting for whoever holds it.
    ///
    /// May block for ever: an implementation is not asked to prove that a
    /// waiting thread ever runs, only that the thread that gets in is alone.
    fn lock(&'a self) -> (ret: Self::Guard)
        ensures
            Self::guard_lock(&ret) == self,
    ;

    /// Releases the lock.
    ///
    /// The data has to satisfy the lock's predicate again: whatever a holder
    /// does to it while holding it, it leaves true what every other thread is
    /// entitled to assume.
    fn unlock(guard: Self::Guard)
        requires
            Self::guard_lock(&guard).inv(Self::guard_view(&guard)),
    ;

    /// Dissolves the lock and returns the data, waiting until it is free.
    fn into_inner(self) -> (ret: T)
        ensures
            self.inv(ret),
    ;
}

} // verus!
