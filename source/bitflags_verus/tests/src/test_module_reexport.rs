// SPDX-License-Identifier: MIT
//! Regression tests for how `bitflags_verus!` interacts with the surrounding
//! module structure and with attributes on individual flags.

/// The macro must work when invoked inside a module other than the crate root,
/// and the generated struct must be re-exportable from that module: `bitflags!`
/// is expanded into a private helper module, so the struct has to be re-exported
/// with the visibility written on it (`pub` here).
mod inner {
    use bitflags_verus::*;

    bitflags_verus! {
        /// Doc comments on the struct are forwarded to `bitflags!`.
        #[derive(Copy, Clone, Debug, Default)]
        pub struct Documented: u64 {
            /// Doc comments on a flag must be forwarded to `bitflags!` too,
            /// which matches per-flag attributes as `ident` plus a token
            /// stream rather than as a single `meta` fragment.
            const FIRST = 0x1;
            #[allow(dead_code)]
            const SECOND = 0x2;
        }
    }
}

pub use inner::Documented;

use vstd::prelude::*;

verus! {

broadcast use bitflags_verus::bitflags_bit_lemmas_u64;

proof fn test_reexported_constants() {
    assert(Documented::FIRST@ == 1u64);
    assert(Documented::SECOND@ == 2u64);
}

fn test_reexported_usage() {
    let mut flags = Documented::empty();
    flags.insert(Documented::FIRST);
    proof {
        assert(flags@ == 0u64 | Documented::FIRST@);
    }
    assert(flags.contains(Documented::FIRST));
}

} // verus!
