// The public items below mention crate-private `RegSpec` on purpose; see its
// docs in `reg_trait.rs`.
#![allow(private_bounds, private_interfaces)]

use vstd::prelude::*;

verus! {

use super::reg_trait::RegSpec;

/// A tracked, thread-affine token owning the current value of one machine
/// register, as seen from *inside* an `asm!` block, where the Rust ABI
/// invariants on register values need not hold.
///
/// Verus cannot verify assembly bodies, so this token is conceptual: it appears
/// only at the trusted `external_body` boundary, where an `asm_*` operation
/// consumes it. Exec code holds `RustRegisterPointsTo` instead.
///
/// The struct is opaque: `reg` and `value` are uninterpreted, so a token has no
/// representation and cannot be constructed anywhere, not even inside this
/// crate.
#[verifier::external_body]
#[verifier::reject_recursive_types(R)]
pub tracked struct AsmRegisterPointsTo<R: RegSpec> {
    reg: core::marker::PhantomData<R>,
    // `*mut ()` is neither `Send` nor `Sync`, so this field pins the token to the
    // thread that created it and prevents it from being shared or moved across
    // threads.
    not_send_sync: core::marker::PhantomData<*mut ()>,
}

impl<R: RegSpec> AsmRegisterPointsTo<R> {
    /// The register marker identifying which register this token owns.
    pub uninterp spec fn reg(&self) -> R;

    pub uninterp spec fn value(&self) -> R::Value;
}

/// The register token exec code holds: an `AsmRegisterPointsTo` that also
/// satisfies `R::rust_abi_wf`, the part of the register's value compiled Rust is
/// entitled to assume at every `asm!` boundary.
#[verifier::reject_recursive_types(R)]
pub tracked struct RustRegisterPointsTo<R: RegSpec> {
    pub(crate) tracked asm: AsmRegisterPointsTo<R>,
}

impl<R: RegSpec> RustRegisterPointsTo<R> {
    /// The register marker identifying which register this token owns.
    pub open(crate) spec fn reg(&self) -> R {
        self.asm.reg()
    }

    pub open(crate) spec fn value(&self) -> R::Value {
        self.asm.value()
    }

    /// Abstract outside the crate, since `rust_abi_wf` is part of the trusted
    /// register model.
    #[verifier::type_invariant]
    pub open(crate) spec fn rust_abi_wf(&self) -> bool {
        R::rust_abi_wf(self.asm.value())
    }
}

} // verus!
