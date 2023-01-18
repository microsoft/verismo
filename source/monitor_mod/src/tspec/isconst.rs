use super::*;

verus! {
    pub trait IsConstant {
        spec fn is_constant(&self) -> bool;

        spec fn is_constant_to(&self, vmpl: nat) -> bool;
    }

    #[verifier(external_body)]
    pub proof fn lemma_is_constant_derive<T: IsConstant, T2: IsConstant>(v: T, f: spec_fn(T) -> T2)
    requires
        v.is_constant() ==> f(v).is_constant()
    {}

    #[verifier(external_body)]
    pub proof fn axiom_default_const<T: SpecDefault + IsConstant>()
    ensures
        (&#[trigger]T::spec_default()).is_constant(),
    {}

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn axiom_const_forall<T: IsConstant>(v: T)
    ensures
        #[trigger]v.is_constant() == v.is_constant_to(1) && v.is_constant_to(2) && v.is_constant_to(3) && v.is_constant_to(4)
    {}
}

#[macro_export]
macro_rules! constant_vars {
    ($($var: ident),* $(,)?) => {
        $(
            $var.is_constant(),
        )*
    }
}
#[macro_export]
macro_rules! impl_spec_constant_for_basic {
    ($($type: ty),* $(,)?) => {
        $(verus!{
            impl IsConstant for $type {
                #[verifier(inline)]
                open spec fn is_constant(&self) -> bool
                {
                    true
                }

                #[verifier(inline)]
                open spec fn is_constant_to(&self, vmpl: nat) -> bool {
                    true
                }
            }
        })*
    }
}
verus! {
impl<T: IsConstant> IsConstant for Option<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool
    {
        self.is_Some() ==> self.get_Some_0().is_constant()
    }

    #[verifier(inline)]
    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        self.is_Some() ==> self.get_Some_0().is_constant_to(vmpl)
    }
}

impl IsConstant for () {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool
    {
        true
    }

    #[verifier(inline)]
    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        true
    }
}

impl<T1: IsConstant, T2: IsConstant> IsConstant for (T1, T2) {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool
    {
        self.0.is_constant() && self.1.is_constant()
    }

    #[verifier(inline)]
    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        self.0.is_constant_to(vmpl) && self.1.is_constant_to(vmpl)
    }
}

impl<T> IsConstant for Ghost<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }

    #[verifier(inline)]
    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        true
    }
}

impl<T> IsConstant for Tracked<T> {
    #[verifier(inline)]
    open spec fn is_constant(&self) -> bool {
        true
    }

    #[verifier(inline)]
    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        true
    }
}

}

impl_spec_constant_for_basic! {u64, u32, u16, usize, u8, bool, char}
