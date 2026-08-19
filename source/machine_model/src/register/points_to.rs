use vstd::prelude::*;

verus! {
    use super::name::*;
    use super::value::*;

    /// Map from register name to the tracked token that owns knowledge of its value.
    pub type RegisterMap = Map<RegName, RegisterPointsTo>;

    /// A tracked, thread-affine permission/token representing knowledge of the current
    /// value of a single machine register.
    ///
    /// There is intentionally no public (or crate-visible) constructor: instances can only
    /// be obtained from whatever external-body operation is responsible for producing them
    /// (e.g. modeling the initial machine state), and can only be consumed/updated through
    /// external-body exec operations taking `Tracked<&mut RegisterPointsTo>`.
    #[verifier::external_body]
    pub tracked struct RegisterPointsTo {
        no_copy: NoCopy,
        // `*mut ()` is neither `Send` nor `Sync`, so this field pins the token to the
        // thread that created it and prevents it from being shared or moved across
        // threads.
        not_send_sync: core::marker::PhantomData<*mut ()>,
    }

    impl RegisterPointsTo {
        pub uninterp spec fn register_id(&self) -> RegName;

        pub uninterp spec fn value(&self) -> RegisterValue;

        /// The value recorded by the token is always well-typed for its register.
        #[verifier::external_body]
        pub broadcast proof fn axiom_value_matches(&self)
            ensures
                #[trigger] self.value().matches(self.register_id()),
        {
        }
    }

    pub broadcast group group_register_points_to_default {
        RegisterPointsTo::axiom_value_matches,
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
