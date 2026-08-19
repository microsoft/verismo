use vstd::prelude::*;

verus! {
    use super::name::*;
    use super::value::*;

    /// Map from register name to the tracked token that owns knowledge of its value.
    pub type RegisterMap = Map<RegName, RegisterPointsTo>;

    /// A tracked, thread-affine permission/token representing knowledge of the current
    /// value of a single machine register.
    ///
    /// The register identity is derived structurally from the stored `RegisterValue`
    /// (see `RegisterValue::register_id`), so mismatched identity/value states are
    /// unrepresentable: there is no separate identity field to disagree with the value.
    ///
    /// There is intentionally no public (or crate-visible) constructor: instances can only
    /// be obtained from whatever external-body operation is responsible for producing them
    /// (e.g. modeling the initial machine state), and can only be consumed/updated through
    /// external-body exec operations taking `Tracked<&mut RegisterPointsTo>`.
    pub tracked struct RegisterPointsTo {
        ghost value: RegisterValue,
        no_copy: no_copy_marker::NoCopyMarker,
        // `*mut ()` is neither `Send` nor `Sync`, so this field pins the token to the
        // thread that created it and prevents it from being shared or moved across
        // threads.
        not_send_sync: core::marker::PhantomData<*mut ()>,
    }

    mod no_copy_marker {
        use vstd::prelude::*;

        /// Opaque wrapper around `vstd`'s `NoCopy` so it can be embedded as a field of
        /// a transparent tracked struct: `NoCopy` itself is a Verus builtin type and
        /// cannot appear directly in a non-`external_body` struct.
        #[verifier::external_body]
        pub struct NoCopyMarker {
            _no_copy: NoCopy,
        }
    }

    impl RegisterPointsTo {
        pub closed spec fn value(&self) -> RegisterValue {
            self.value
        }

        pub open spec fn register_id(&self) -> RegName {
            self.value().register_id()
        }
    }
}

#[cfg(feature = "reject-send")]
mod reject_send {
    use super::RegisterPointsTo;

    fn require_send<T: Send>() {}

    fn check() {
        require_send::<RegisterPointsTo>();
    }
}

#[cfg(feature = "reject-sync")]
mod reject_sync {
    use super::RegisterPointsTo;

    fn require_sync<T: Sync>() {}

    fn check() {
        require_sync::<RegisterPointsTo>();
    }
}
