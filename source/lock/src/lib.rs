//! A spin lock built on atomics, with the guarantee that a lock really
//! excludes.
//!
//! [`SpinLock`] is fair: it is a ticket lock, so threads take the lock in the
//! order they asked for it and none is passed over.
//!
//! # The two layers
//!
//! The lock comes in two forms. The *raw* form, [`RawSpinLock`], guards
//! nothing but tracked ghost state: acquiring hands the state out, releasing
//! takes it back, and nothing else can produce it. That is what a lock
//! guarding memory the caller owns elsewhere needs, and it is what an
//! implementation of a per-object lock contract is written against.
//!
//! The *data* form, [`SpinLock`], is the raw form over a cell, and has the
//! shape `std::sync::Mutex` has: the lock owns its value, `lock` returns a
//! guard, and the guard derefs to the value.
//!
//! # Using a different lock
//!
//! [`SpinLockTrait`] is what the data form promises, as a trait. An embedder
//! whose system already has a lock -- one its scheduler knows about, or one
//! the hardware offers -- implements that trait instead of using [`SpinLock`],
//! and whatever was written against the trait keeps verifying unchanged.
//!
//! # What "excludes" means here
//!
//! The lock is proved to hand out its contents to one holder at a time,
//! because the contents are a *tracked* value: there is only ever one of it,
//! and a thread that has it can only give it back. Releasing needs proof of
//! holding as well, so a thread that is not the holder cannot let anyone in.
//!
//! Nothing here proves liveness -- a thread that never releases blocks every
//! other one, and the spinning is unbounded. [`RawSpinLock::acquire`] is the
//! only place in the crate where Verus's termination check is switched off,
//! and it is the only reason it is switched off anywhere.
//!
//! Release is explicit. A guard that is dropped rather than released leaks the
//! lock; Verus does not check that a guard is used, which is the same caveat
//! `vstd::rwlock` carries.
//!
//! # What the value must satisfy
//!
//! A lock is parameterised by a predicate over what it guards, in the style of
//! `vstd::rwlock`: whatever goes in must satisfy it, and whatever comes out is
//! known to. A lock over data whose contents are unconstrained instantiates
//! the predicate with `|v| true`.
#![no_std]
#![cfg_attr(verus_only, feature(sized_hierarchy))]
#![feature(proc_macro_hygiene)]
#![cfg_attr(not(verus_only), feature(stmt_expr_attributes))]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]
// Without Verus the ghost arguments and assignments are all that is left of
// the proofs, and the state machines' modules are named after their types.
#![cfg_attr(
    not(verus_only),
    allow(unused_variables, unused_assignments, non_shorthand_field_patterns)
)]
#![allow(non_snake_case)]
#![cfg_attr(verus_only, allow(macro_expanded_macro_exports_accessed_by_absolute_paths))]
#![allow(unused_braces)]

use builtin_macros::*;

pub mod pred;
pub mod spin;
pub mod spin_spec;
pub mod spin_tok;
pub mod spin_contract;

pub use pred::LockPredicate;
pub use spin::{Hold, RawSpinLock, SpinGuard, SpinLock, Ticket};
pub use spin_contract::{SpinLockSpec, SpinLockTrait};
