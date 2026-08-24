//! Spinning locks built on atomics, with the guarantee that a lock really
//! excludes.
//!
//! [`SpinLock`] is fair: it is a ticket lock, so threads take the lock in the
//! order they asked for it and none is passed over. [`RwLock`] is not -- a
//! stream of readers can keep a writer waiting.
//!
//! # The two layers
//!
//! Each lock comes in two forms. The *raw* form -- [`RawSpinLock`] and
//! [`RawRwLock`] -- guards nothing but tracked ghost state: acquiring hands
//! the state out, releasing takes it back, and nothing else can produce it.
//! That is what a lock guarding memory the caller owns elsewhere needs, and it
//! is what an implementation of a per-object lock contract is written against.
//!
//! The *data* form -- [`SpinLock`] and [`RwLock`] -- is the raw form over a
//! cell, and has the shape `std::sync::Mutex` and `std::sync::RwLock` have:
//! the lock owns its value, `lock` returns a guard, and the guard derefs to
//! the value.
//!
//! # What "excludes" means here
//!
//! Both locks are proved to hand out their contents to one holder at a time,
//! because the contents are a *tracked* value: there is only ever one of it,
//! and a thread that has it can only give it back. Releasing needs proof of
//! holding as well, so a thread that is not the holder cannot let anyone in.
//!
//! Nothing here proves liveness -- a thread that never releases blocks every
//! other one, and the spinning is unbounded. The three blocking acquires
//! ([`RawSpinLock::acquire`], [`RawRwLock::acquire_write`] and
//! [`RawRwLock::acquire_read`]) are the only places in the crate where Verus's
//! termination check is switched off, and they are the only reason it is
//! switched off anywhere.
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
#![cfg_attr(verus_keep_ghost, feature(sized_hierarchy))]
#![feature(proc_macro_hygiene)]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]
#![cfg_attr(verus_only, allow(macro_expanded_macro_exports_accessed_by_absolute_paths))]
#![allow(unused_braces)]

use builtin_macros::*;

pub mod pred;
pub mod rwlock;
pub mod spin;
pub mod spin_tok;

pub use pred::LockPredicate;
pub use rwlock::{RawRwLock, ReadGuard, RwLock, WriteGuard};
pub use spin::{Hold, RawSpinLock, SpinGuard, SpinLock, Ticket};
