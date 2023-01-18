use super::*;

verus! {
pub ghost struct RegisterPermValue<T> {
    // Identifier
    pub cpu: nat,
    pub id: RegName,
    pub shared: bool,
    // Verismo software tracked value
    pub value: T,
}

impl<T> RegisterPermValue<T> {
    pub open spec fn shared(&self) -> bool {
        self.shared
    }

    pub open spec fn value(&self) -> T {
        self.value
    }
}
impl<T: WellFormed + IsConstant> RegisterPermValue<T> {
    pub open spec fn spec_write_value(self, prev: Self, val: T) -> bool {
        &&& prev.cpu == self.cpu
        &&& prev.id == self.id
        &&& prev.shared() == self.shared()
        &&& self.value() === val
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.shared() ==> self.value().is_constant()
        &&& self.value().wf()
    }
}

#[verifier(external_body)]
pub tracked struct RegisterPerm {
    no_copy: NoCopy,
}

impl RegisterPerm {
    pub open spec fn view<T>(&self) -> RegisterPermValue<T> {
        RegisterPermValue {
            value: self.val(),
            cpu: self.cpu(),
            id: self.id(),
            shared: self.shared(),
        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_eq<T>(x: Self, y: Self)
    requires
        x.view::<T>() === y.view::<T>(),
    ensures
        x === y
    {}

    pub spec fn cpu(&self) -> nat;
    pub spec fn id(&self) -> RegName;
    pub spec fn shared(&self) -> bool;
    pub spec fn val<T>(&self) -> T where T: core::marker::Sized;

    pub spec fn wf(&self) -> bool;

    #[verifier(inline)]
    pub open spec fn wf_notshared(&self) -> bool {
        &&& self.wf()
        &&& !self.shared()
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_wf<T: WellFormed + IsConstant>(&self)
    ensures
        self.wf() == self.view::<T>().wf()
    {}

    pub open spec fn is_ghcb(&self) -> bool {
        let ghcb_perm_view: RegisterPermValue<u64> = self@;
        &&& ghcb_perm_view.value.is_constant()
        &&& ghcb_perm_view.id === RegName::MSR(MSR_GHCB_BASE)
        &&& ghcb_perm_view.wf()
        &&& ghcb_perm_view.shared()
    }
}
}
