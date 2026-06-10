// SPDX-License-Identifier: MIT OR Apache-2.0
//
// Author: Ziqiao Zhou <ziqiaozhou@microsoft.com>
//
// External specifications for the `bitflags` crate traits.
#![cfg(verus_only)]
use bitflags::Bits;
use vstd::prelude::*;

verus! {

pub uninterp spec fn spec_from_bits_retain<B, T>(bits: B) -> T;

pub broadcast axiom fn axiom_from_bits_retain<T>(bits: T::Bits) where T: bitflags::Flags
    ensures
        T::obeys_bitflags_spec() ==> (#[trigger] spec_from_bits_retain::<T::Bits, T>(
            bits,
        )).bits_spec() == bits,
;

#[verifier::external_trait_specification]
pub trait ExBits: Clone + Copy + core::cmp::PartialEq + core::ops::BitAnd<
    Output = Self,
> + core::ops::BitOr<Output = Self> + core::ops::BitXor<Output = Self> + core::ops::Not<
    Output = Self,
> + Sized + 'static {
    type ExternalTraitSpecificationFor: bitflags::Bits;
}

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(FlagsSpec via FlagsSpecImpl)]
pub trait ExFlags: Sized + 'static {
    type ExternalTraitSpecificationFor: bitflags::Flags;

    /// The underlying bits type.
    type Bits: bitflags::Bits;

    spec fn obeys_bitflags_spec() -> bool;

    spec fn bits_spec(&self) -> Self::Bits;

    fn from_bits_retain(bits: Self::Bits) -> (ret: Self)
        ensures
            Self::obeys_bitflags_spec() ==> ret == spec_from_bits_retain::<Self::Bits, Self>(bits),
    ;

    fn bits(&self) -> (ret: Self::Bits)
        ensures
            Self::obeys_bitflags_spec() ==> ret == self.bits_spec(),
    ;
}

} // verus!
