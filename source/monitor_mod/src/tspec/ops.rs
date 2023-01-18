use super::*;

verus! {
pub trait VSpecOrd<Rhs> {
    spec fn spec_lt(self, rhs: Rhs) -> bool where Self: core::marker::Sized;

    spec fn spec_le(self, rhs: Rhs) -> bool where Self: core::marker::Sized;

    spec fn spec_gt(self, rhs: Rhs) -> bool where Self: core::marker::Sized;

    spec fn spec_ge(self, rhs: Rhs) -> bool where Self: core::marker::Sized;
}

pub trait VSpecEq<Rhs> {
    spec fn spec_eq(self, rhs: Rhs) -> bool where Self: core::marker::Sized;
}

pub trait VSpecNeg {
    spec fn spec_neg(self) -> Self where Self: core::marker::Sized;
}

pub trait VSpecNot {
    spec fn spec_not(self) -> Self where Self: core::marker::Sized;
}

pub trait VSpecAdd<Rhs, Output> {
    spec fn spec_add(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecSub<Rhs, Output> {
    spec fn spec_sub(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecMul<Rhs, Output> {
    spec fn spec_mul(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecEuclideanDiv<Rhs, Output> {
    spec fn spec_euclidean_div(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecEuclideanMod<Rhs, Output> {
    spec fn spec_euclidean_mod(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecBitAnd<Rhs, Output> {
    spec fn spec_bitand(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecBitOr<Rhs, Output> {
    spec fn spec_bitor(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecBitXor<Rhs, Output> {
    spec fn spec_bitxor(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecShl<Rhs, Output> {
    spec fn spec_shl(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

pub trait VSpecShr<Rhs, Output> {
    spec fn spec_shr(self, rhs: Rhs) -> Output where Self: core::marker::Sized;
}

#[macro_export]
macro_rules! impl_spec_not_for_basic {
    ($($type: ty),* $(,)?) => {
        $(verus!{
            impl VSpecNot for $type {
                #[verifier(inline)]
                open spec fn spec_not(self) -> Self
                {
                    !self
                }
            }
        })*
    }
}

impl_spec_not_for_basic!{u64, u32, u16, usize, u8, bool}

impl VSpecEq<bool> for bool {
    #[verifier(inline)]
    open spec fn spec_eq(self, rhs: bool) -> bool {
        self == rhs
    }
}
}
