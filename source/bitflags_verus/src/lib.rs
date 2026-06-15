// SPDX-License-Identifier: MIT
//! # bitflags_verus
//!
//! Formal [Verus](https://github.com/verus-lang/verus) specifications for
//! Rust's [`bitflags`](https://docs.rs/bitflags) crate.
//!
//! This crate provides the [`bitflags_verus!`] macro, a drop-in wrapper around
//! `bitflags::bitflags!` that additionally emits Verus `assume_specification`
//! annotations for every generated method and operator. This lets you write
//! verified code that reasons about bitflags values using their underlying
//! integer representation—without giving up the ergonomics of `bitflags`.
//!
//! ## Limitations
//!
//! - **Unverified assumptions.** All specifications are provided via
//!   `assume_specification` (i.e., trusted axioms) rather than verified proofs.
//!   Verus currently cannot inject proof code into macro-generated function
//!   bodies from external crates, so the correctness of these specs relies on
//!   manual review against the `bitflags` implementation, not machine-checked
//!   proofs.
//!
//! - **Incomplete coverage.** This crate may not provide specifications for
//!   every method or trait impl that `bitflags!` generates. In particular,
//!   iterator-related methods, `Debug`/`Display` formatting, and
//!   `FromIterator` are not currently specified.
//!
//! ## Design
//!
//! Each bitflags struct is modeled as an opaque type with a single
//! `spec fn view(self) -> Bits` that maps to the underlying integer value.
//! All specifications are expressed in terms of `view()`:
//!
//! - `flags.union(other).view() == flags.view() | other.view()`
//! - `flags.contains(other) <==> (flags.view() & other.view()) == other.view()`
//! - `flags.complement().view() == (!flags.view()) & Flags::all().view()`
//!
//! A single foundational axiom ([`axiom_from_bits_retain`](traits::axiom_from_bits_retain))
//! bridges the opaque struct to concrete bit values:
//! `spec_from_bits_retain(bits).view() == bits`.
//!
//! ## Quick Start
//!
//! Add to your `Cargo.toml`:
//! ```toml
//! [dependencies]
//! bitflags = "2"
//! bitflags_verus = "0.1"
//! ```
//!
//! Then define flags with full Verus specifications:
//! ```ignore
//! use bitflags_verus::*;
//!
//! bitflags_verus! {
//!     #[derive(Copy, Clone, Debug, Default)]
//!     pub struct Permissions: u32 {
//!         const READ    = 1 << 0;
//!         const WRITE   = 1 << 1;
//!         const EXECUTE = 1 << 2;
//!     }
//! }
//!
//! verus! {
//!     fn example() {
//!         let mut p = Permissions::empty();
//!         p.insert(Permissions::READ);
//!         p.insert(Permissions::WRITE);
//!         assert(p.contains(Permissions::WRITE));
//!
//!         let old = p.bits();
//!         p.remove(Permissions::WRITE);
//!         proof {
//!             assert(p@ == old & !Permissions::WRITE@);
//!         }
//!     }
//! }
//! ```
//!
//! ## What Gets Specified
//!
//! The macro emits specifications for:
//!
//! | Category | Methods |
//! |----------|---------|
//! | Construction | `empty`, `all`, `from_bits`, `from_bits_truncate`, `from_bits_retain` |
//! | Queries | `bits`, `is_empty`, `is_all`, `contains`, `intersects` |
//! | Set operations | `union`, `intersection`, `difference`, `symmetric_difference`, `complement` |
//! | Mutation | `insert`, `remove`, `toggle`, `set` |
//! | Operators | `\|`, `&`, `^`, `-`, `!`, `\|=`, `&=`, `^=`, `-=` |
//! | Constants | Each named flag (e.g., `Flags::READ`) |
//!
//! ## Broadcast Lemmas
//!
//! This crate provides per-type broadcast groups (`bitflags_bit_lemmas_<type>`)
//! with commonly needed bit-vector identities that Verus's SMT solver cannot
//! prove automatically:
//!
//! - **OR-AND absorption:** `(a | b) & b == b`
//! - **OR preserves subset:** `(a & b) == b ==> (a | c) & b == b`
//! - **Difference clears bits:** `(a & !b) & b == 0`
//!
//! These are generated for `u8`, `u16`, `u32`, `u64`, `usize`, `i32`, and
//! `isize`. The macro automatically imports the group matching your struct's
//! underlying type. For use in your own `verus!` blocks, import explicitly:
//!
//! ```ignore
//! verus! {
//!     broadcast use bitflags_verus::bitflags_bit_lemmas_u32;
//! }
//! ```
//!
//! ## Using `#[verus_spec]` with Existing Functions
//!
//! You can annotate existing functions that take or return bitflags with
//! `#[verus_spec]` to add pre/postconditions using the `view()` model:
//!
//! ```ignore
//! #[cfg(verus_only)]
//! use bitflags_verus::bitflags_verus as bitflags;
//! #[cfg(not(verus_only))]
//! use bitflags::bitflags;
//!
//! bitflags! {
//!     #[derive(Copy, Clone, Debug, Default)]
//!     pub struct Permissions: u32 {
//!         const READ    = 1 << 0;
//!         const WRITE   = 1 << 1;
//!         const EXECUTE = 1 << 2;
//!     }
//! }
//!
//! #[verus_spec(
//!     ensures *final(perms) == spec_union(*old(perms), Permissions::READ),
//! )]
//! fn grant_read(perms: &mut Permissions) {
//!     perms.insert(Permissions::READ);
//! }
//!
//! #[verus_spec(
//!     ensures *final(perms) == spec_difference(*old(perms), Permissions::WRITE),
//! )]
//! fn revoke_write(perms: &mut Permissions) {
//!     perms.remove(Permissions::WRITE);
//! }
//!
//! #[verus_spec(ret =>
//!     ensures ret == ((perms@ & Permissions::EXECUTE@) == Permissions::EXECUTE@),
//! )]
//! fn has_execute(perms: &Permissions) -> bool {
//!     perms.contains(Permissions::EXECUTE)
//! }
//! ```
//!
//! ## Supported Underlying Types
//!
//! Any integer type supported by `bitflags`: `u8`, `u16`, `u32`, `u64`,
//! `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128`, `isize`.
#![no_std]

pub mod traits;
pub use vstd::prelude::*;

verus! {

#[cfg(verus_only)]
pub use traits::spec_from_bits_retain;
#[cfg(verus_only)]
pub use traits::FlagsSpec;

/// Core broadcast group auto-imported by all consumers of this crate.
///
/// Contains [`axiom_from_bits_retain`](traits::axiom_from_bits_retain), the
/// foundational axiom that connects the opaque bitflags struct to its
/// underlying bit representation: `spec_from_bits_retain(bits).view() == bits`.
#[cfg_attr(verus_only, verifier::broadcast_use_by_default_when_this_crate_is_imported)]
pub broadcast group bigflags_axioms {
    traits::axiom_from_bits_retain,
}

} // verus!
/// Generate broadcast proofs for bit-vector identities for a single integer type.
///
/// Each invocation produces three broadcast lemmas and one broadcast group:
/// - `lemma_bitor_band_absorb_<T>`: `(a | b) & b == b`
/// - `lemma_bitor_preserves_subset_<T>`: `(a & b) == b ==> (a | c) & b == b`
/// - `lemma_band_not_clears_<T>`: `(a & !b) & b == 0`
/// - `bitflags_bit_lemmas_<T>`: group containing all three
macro_rules! bitflags_bit_lemmas {
    ($($suffix:ident : $uN:ty),* $(,)?) => {
        paste! { verus! { $(
            /// OR-AND absorption: `(a | b) & b == b`
            pub broadcast proof fn [<lemma_bitor_band_absorb_ $suffix>](a: $uN, b: $uN)
                ensures #[trigger] ((a | b) & b) == b
            { assert((a | b) & b == b) by(bit_vector); }

            /// OR preserves subset: if `(a & b) == b` then `((a | c) & b) == b`
            pub broadcast proof fn [<lemma_bitor_preserves_subset_ $suffix>](a: $uN, b: $uN, c: $uN)
                requires (a & b) == b,
                ensures #[trigger] ((a | c) & b) == b
            { assert((a & b) == b ==> (a | c) & b == b) by(bit_vector); }

            /// Difference clears target bits: `(a & !b) & b == 0`
            pub broadcast proof fn [<lemma_band_not_clears_ $suffix>](a: $uN, b: $uN)
                ensures #[trigger] ((a & !b) & b) == (0 as $uN)
            { assert((a & !b) & b == (0 as $uN)) by(bit_vector); }

            /// Per-type broadcast group for bit-vector lemmas.
            pub broadcast group [<bitflags_bit_lemmas_ $suffix>] {
                [<lemma_bitor_band_absorb_ $suffix>],
                [<lemma_bitor_preserves_subset_ $suffix>],
                [<lemma_band_not_clears_ $suffix>],
            }
        )* }
}
    };
}

bitflags_bit_lemmas!(u8: u8, u16: u16, u32: u32, u64: u64, usize: usize, i32: i32, isize: isize);

/// Define a bitflags struct with full Verus formal specifications.
///
/// This macro wraps [`bitflags::bitflags!`] and emits Verus
/// `assume_specification` annotations for all generated methods, operators,
/// and named constants. The specifications model each flags value as an
/// opaque type with `spec fn view(self) -> Bits` returning the underlying
/// integer representation.
///
/// # Syntax
///
/// Identical to `bitflags::bitflags!`:
///
/// ```ignore
/// bitflags_verus! {
///     #[derive(Copy, Clone, Debug, Default)]
///     pub struct MyFlags: u32 {
///         const A = 1 << 0;
///         const B = 1 << 1;
///         const C = 1 << 2;
///     }
/// }
/// ```
///
/// # Requirements
///
/// Your crate must depend on `bitflags` (version 2.x) directly—this macro
/// invokes `::bitflags::bitflags!` from the consumer's namespace.
///
/// # Generated Specifications
///
/// For each struct, the macro generates:
/// - `spec fn view(self) -> Bits` — the underlying integer value
/// - `spec fn spec_all() -> Self` — all defined flags OR'd together
/// - `spec fn spec_empty() -> Self` — zero value
/// - Inline specs for all set operations (`spec_union`, `spec_intersection`, etc.)
/// - `assume_specification` for every exec method and operator
/// - `spec const SPEC_<FLAG>` for each named constant
/// - Operator trait impls (`BitOrSpecImpl`, `BitAndSpecImpl`, etc.)
///
/// # Example (Verus verification)
///
/// ```ignore
/// verus! {
///     // Import bit-vector lemmas for the underlying type
///     broadcast use bitflags_verus::bitflags_bit_lemmas_u32;
///
///     proof fn union_is_bitor(a: MyFlags, b: MyFlags) {
///         assert(a.union(b)@ == a@ | b@);
///     }
///
///     proof fn contains_is_subset(flags: MyFlags, check: MyFlags) {
///         assert(flags.contains(check) == ((flags@ & check@) == check@));
///     }
/// }
/// ```
#[macro_export]
macro_rules! bitflags_verus {
    (
        $(#[$outer:meta])*
        $vis:vis struct $name:ident : $bits:ty {
            $(
                $(#[$cmeta:meta])*
                const $cname:ident = $cvalue:expr;
            )*
        }
    ) => {
        paste! {
        mod [<spec_ $name _internal>] {
            use super::*;
            ::bitflags::bitflags! {
                    $(#[$outer])*
                    $vis struct $name : $bits {
                        $(
                            $(#[$cmeta])*
                            const $cname = $cvalue;
                        )*
                    }
            }

            $crate::__bitflags_verus_one! {
                $name, $bits, [ $( $cname = ($cvalue) ),* ]
            }
            }
            use [<spec_ $name _internal>]::*;
        }
    };
}

/// Internal helper macro for [`bitflags_verus!`]. Do not use directly.
///
/// Emits all Verus specifications for a single bitflags struct: the
/// `external_type_specification`, `FlagsSpecImpl`, spec mirrors,
/// `assume_specification` annotations, and operator trait impls.
#[doc(hidden)]
#[macro_export]
macro_rules! __bitflags_verus_one {
    ($name:ident, $bits:ty, [ $( $cname:ident = ($cvalue:expr) ),* $(,)? ]) => {
        #[cfg(verus_only)]
        $crate::paste! {$crate::verus! {
            use super::*;
            impl $name {
                #[verifier::inline]
                pub open spec fn view(self) -> $bits {
                    self.bits_spec()
                }
            }
            /// Register the bitflags-emitted struct as a Verus-known
            /// external type so an inherent `spec fn` can be added.
            #[verifier::external_type_specification]
            #[verifier::external_body]
            pub struct ExBitflagsView($name);
                // -- spec mirrors used by `when_used_as_spec` ----------------
                //
                // For every exec method that takes only spec-friendly inputs
                // and returns a spec-friendly value, define a `spec_<method>`
                // free function with the same signature.  The matching
                // `#[verifier::when_used_as_spec(spec_<method>)]` attribute
                // on the `assume_specification` then lets calls to the exec
                // method appear in `requires`/`ensures` and `#[verus_spec]`
                // positions.

                #[verifier::inline]
                pub open spec fn spec_all() -> $name {
                    $crate::spec_from_bits_retain((0 as $bits) $( | ($cvalue as $bits) )*)
                }

                #[verifier::inline]
                pub open spec fn spec_empty() -> $name {
                    $crate::spec_from_bits_retain(0 as $bits)
                }

                pub open spec fn spec_bits(s: &$name) -> $bits {
                    s.view()
                }

                #[verifier::inline]
                pub open spec fn spec_from_bits_truncate(bits: $bits) -> $name {
                    $crate::spec_from_bits_retain(bits & spec_all().view())
                }

                #[verifier::inline]
                pub open spec fn spec_from_bits(bits: $bits) -> Option<$name> {
                    if bits == (bits & spec_all().view()) {
                        Some($crate::spec_from_bits_retain(bits))
                    } else {
                        None
                    }
                }

                pub open spec fn spec_is_empty(s: &$name) -> bool {
                    s.view() == 0 as $bits
                }

                pub open spec fn spec_is_all(s: &$name) -> bool {
                    (s.view() | $name::all().view()) == s.view()
                }

                pub open spec fn spec_intersects(s: &$name, other: $name) -> bool {
                    s.view() & other.view() != 0 as $bits
                }

                pub open spec fn spec_contains(s: &$name, other: $name) -> bool {
                    (s.view() & other.view()) == other.view()
                }

                #[verifier::inline]
                pub open spec fn spec_intersection(s: $name, other: $name) -> $name {
                    $crate::spec_from_bits_retain(s.view() & other.view())
                }

                #[verifier::inline]
                pub open spec fn spec_union(s: $name, other: $name) -> $name {
                    $crate::spec_from_bits_retain(s.view() | other.view())
                }

                #[verifier::inline]
                pub open spec fn spec_difference(s: $name, other: $name) -> $name {
                    $crate::spec_from_bits_retain(s.view() & !other.view())
                }

                #[verifier::inline]
                pub open spec fn spec_symmetric_difference(s: $name, other: $name) -> $name {
                    $crate::spec_from_bits_retain(s.view() ^ other.view())
                }

                #[verifier::inline]
                pub open spec fn spec_complement(s: $name) -> $name {
                    $crate::spec_from_bits_retain((!s.view()) & spec_all().view())
                }

                #[verifier::inline]
                pub open spec fn spec_from_bits_retain(bits: $bits) -> $name {
                    $crate::spec_from_bits_retain(bits)
                }

                $(
                    pub spec const [<SPEC_$cname>]: $name = spec_from_bits_retain($cvalue as $bits);
                    #[allow(non_snake_case)]
                    #[verifier::when_used_as_spec([<SPEC_$cname>])]
                    pub assume_specification[ $name::$cname ] -> (r: $name)
                        ensures r == [<SPEC_$cname>];
                )*

                // -- assume_specifications, each tied to its spec mirror -----

                #[verifier::when_used_as_spec(spec_all)]
                pub assume_specification[ $name::all ]() -> (r: $name)
                    ensures r == spec_all();

                #[verifier::when_used_as_spec(spec_empty)]
                pub assume_specification[ $name::empty ]() -> (r: $name)
                    ensures r.view() == 0 as $bits;

                #[verifier::when_used_as_spec(spec_bits)]
                pub assume_specification[ $name::bits ](s: &$name) -> (r: $bits)
                    ensures r == s.view();

                #[verifier::when_used_as_spec(spec_from_bits_retain)]
                pub assume_specification[ $name::from_bits_retain ](bits: $bits)
                    -> (r: $name)
                    ensures
                        r === spec_from_bits_retain(bits),
                        r.view() == bits;

                #[verifier::when_used_as_spec(spec_from_bits_truncate)]
                pub assume_specification[ $name::from_bits_truncate ](bits: $bits)
                    -> (r: $name)
                    ensures
                        r == spec_from_bits_truncate(bits),
                        r.view() == (bits & $name::all().view());

                #[verifier::when_used_as_spec(spec_from_bits)]
                pub assume_specification[ $name::from_bits ](bits: $bits)
                    -> (r: Option<$name>)
                    ensures
                        r == spec_from_bits(bits),
                        r.is_some() == (bits == (bits & $name::all().view())),
                        match r {
                            Some(v) => v.view() == bits,
                            None => true,
                        };

                #[verifier::when_used_as_spec(spec_is_empty)]
                pub assume_specification[ $name::is_empty ](s: &$name) -> (r: bool)
                    ensures r == spec_is_empty(s);

                #[verifier::when_used_as_spec(spec_is_all)]
                pub assume_specification[ $name::is_all ](s: &$name) -> (r: bool)
                    ensures r == spec_is_all(s);

                #[verifier::when_used_as_spec(spec_intersects)]
                pub assume_specification[ $name::intersects ](s: &$name, other: $name)
                    -> (r: bool)
                    ensures r == spec_intersects(s, other);

                #[verifier::when_used_as_spec(spec_contains)]
                pub assume_specification[ $name::contains ](s: &$name, other: $name)
                    -> (r: bool)
                    ensures r == spec_contains(s, other);

                #[verifier::when_used_as_spec(spec_intersection)]
                pub assume_specification[ $name::intersection ](s: $name, other: $name)
                    -> (r: $name)
                    ensures
                        r == spec_intersection(s, other),
                        r.view() == s.view() & other.view();

                #[verifier::when_used_as_spec(spec_union)]
                pub assume_specification[ $name::union ](s: $name, other: $name)
                    -> (r: $name)
                    ensures
                        r == spec_union(s, other),
                        r.view() == s.view() | other.view();

                #[verifier::when_used_as_spec(spec_difference)]
                pub assume_specification[ $name::difference ](s: $name, other: $name)
                    -> (r: $name)
                    ensures
                        r == spec_difference(s, other),
                        r.view() == s.view() & !other.view();

                #[verifier::when_used_as_spec(spec_symmetric_difference)]
                pub assume_specification[ $name::symmetric_difference ](s: $name, other: $name)
                    -> (r: $name)
                    ensures
                        r == spec_symmetric_difference(s, other),
                        r.view() == s.view() ^ other.view();

                #[verifier::when_used_as_spec(spec_complement)]
                pub assume_specification[ $name::complement ](s: $name) -> (r: $name)
                    ensures
                        r == spec_complement(s),
                        r.view() == (!s.view()) & $name::all().view();

                // Mutating methods (no `when_used_as_spec` — they return ()).

                pub assume_specification[ $name::insert ](s: &mut $name, other: $name)
                    ensures *final(s) == spec_union(*old(s), other);

                pub assume_specification[ $name::remove ](s: &mut $name, other: $name)
                    ensures *final(s) == spec_difference(*old(s), other);

                pub assume_specification[ $name::toggle ](s: &mut $name, other: $name)
                    ensures *final(s) == spec_symmetric_difference(*old(s), other);

                pub assume_specification[ $name::set ](
                    s: &mut $name, other: $name, value: bool,
                )
                    ensures
                        *final(s) == if value {
                            spec_union(*old(s), other)
                        } else {
                            spec_difference(*old(s), other)
                        };

                // -- include operators even when they are defined outside the verus! ------
                impl $crate::traits::FlagsSpecImpl for $name {
                    open spec fn obeys_bitflags_spec() -> bool { true }
                    uninterp spec fn bits_spec(&self) -> Self::Bits;
                }

                impl vstd::std_specs::ops::BitOrSpecImpl for $name {
                    open spec fn obeys_bitor_spec() -> bool { true }
                    open spec fn bitor_req(self, other: $name) -> bool { true }
                    open spec fn bitor_spec(self, other: $name) -> $name {
                        spec_union(self, other)
                    }
                }
                impl vstd::std_specs::ops::BitAndSpecImpl for $name {
                    open spec fn obeys_bitand_spec() -> bool { true }
                    open spec fn bitand_req(self, other: $name) -> bool { true }
                    open spec fn bitand_spec(self, other: $name) -> $name {
                        spec_intersection(self, other)
                    }
                }
                impl vstd::std_specs::ops::BitXorSpecImpl for $name {
                    open spec fn obeys_bitxor_spec() -> bool { true }
                    open spec fn bitxor_req(self, other: $name) -> bool { true }
                    open spec fn bitxor_spec(self, other: $name) -> $name {
                        spec_symmetric_difference(self, other)
                    }
                }
                impl vstd::std_specs::ops::SubSpecImpl for $name {
                    open spec fn obeys_sub_spec() -> bool { true }
                    open spec fn sub_req(self, other: $name) -> bool { true }
                    open spec fn sub_spec(self, other: $name) -> $name {
                        spec_difference(self, other)
                    }
                }
                impl vstd::std_specs::ops::NotSpecImpl for $name {
                    open spec fn obeys_not_spec() -> bool { true }
                    open spec fn not_req(self) -> bool { true }
                    open spec fn not_spec(self) -> $name {
                        spec_complement(self)
                    }
                }
                pub assume_specification[ <$name as ::core::ops::BitOr>::bitor ](
                    s: $name, other: $name,
                ) -> (r: $name);

                pub assume_specification[ <$name as ::core::ops::BitAnd>::bitand ](
                    s: $name, other: $name,
                ) -> (r: $name);

                pub assume_specification[ <$name as ::core::ops::BitXor>::bitxor ](
                    s: $name, other: $name,
                ) -> (r: $name);

                pub assume_specification[ <$name as ::core::ops::Sub>::sub ](
                    s: $name, other: $name,
                ) -> (r: $name);

                pub assume_specification[ <$name as ::core::ops::Not>::not ](s: $name)
                    -> (r: $name);

                pub assume_specification[ <$name as ::core::ops::BitOrAssign>::bitor_assign ](
                    s: &mut $name, other: $name,
                );

                pub assume_specification[ <$name as ::core::ops::BitAndAssign>::bitand_assign ](
                    s: &mut $name, other: $name,
                );

                pub assume_specification[ <$name as ::core::ops::BitXorAssign>::bitxor_assign ](
                    s: &mut $name, other: $name,
                );

                pub assume_specification[ <$name as ::core::ops::SubAssign>::sub_assign ](
                    s: &mut $name, other: $name,
                );
            }
}
    };
}

#[doc(hidden)]
pub use paste::paste;
