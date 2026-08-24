//! Proof helpers shared across the verified crates in this workspace.
#![no_std]
#![allow(unused_braces)]
#![cfg_attr(not(verus_only), allow(dead_code, unused_imports))]

use builtin_macros::*;

// Lemmas only; the items they are about exist only under Verus.
#[cfg(verus_only)]
pub mod bits;

/// Build a `Tracked<V>` in exec code annotated with attributes.
///
/// Attribute-style exec code cannot name `Tracked(..)` directly; it has to go
/// through `verus_exec_expr!`, which is easy to reach for too widely. This
/// wraps exactly the one thing that needs it.
///
/// `Tracked` must be in scope at the call site: Verus recognises the
/// constructor only as a bare name, so the macro cannot spell out its path.
#[macro_export]
macro_rules! tracked {
    ($e:expr) => {
        ::builtin_macros::verus_exec_expr! { Tracked($e) }
    };
}

/// Build a `Ghost<V>` in exec code annotated with attributes. See [`tracked!`].
#[macro_export]
macro_rules! ghost {
    ($e:expr) => {
        ::builtin_macros::verus_exec_expr! { Ghost($e) }
    };
}

verus! {

global size_of usize == 8;

} // verus!
