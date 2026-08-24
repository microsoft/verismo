//! What a lock promises about the thing it guards.
use vstd::prelude::*;

verus! {

/// The property a lock's contents always have, when no one is holding them.
///
/// A lock is a place where a value waits for its next holder, and the
/// predicate is what every holder promises to leave true. It is a *value*
/// rather than only a type so that a lock can be constrained by something
/// decided at run time -- the identity of the page it guards, say -- and not
/// only by something decided when the code was written.
///
/// Implemented for `spec_fn(V) -> bool`, which is the closure-shaped way to
/// say it and the one to reach for when the constraint is not worth a name.
pub trait LockPredicate<V>: Sized {
    spec fn inv(self, v: V) -> bool;
}

impl<V> LockPredicate<V> for spec_fn(V) -> bool {
    open spec fn inv(self, v: V) -> bool {
        self(v)
    }
}

} // verus!
