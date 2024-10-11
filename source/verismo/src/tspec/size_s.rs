use vstd::prelude::*;

use super::*;

macro_rules! impl_spec_size_for_basic  {
    ($([$baset: ty, $size: literal]),* $(,)*) => {
        $(
        verus!{
            impl SpecSize for $baset {
                #[verifier(inline)]
                open spec fn spec_size_def() -> nat
                {
                    $size
                }
            }
        }
        )*
    };
}
verus! {

pub open spec fn spec_max_count<T>() -> nat;

// pub spec fn spec_field_offset<T>(i: nat) -> nat;
pub trait SpecSize {
    spec fn spec_size_def() -> nat;
}

// For core::mem:sizeof
pub open spec fn spec_size<T>() -> nat;

pub trait ExecStruct {

}

impl ExecStruct for u8 {

}

impl ExecStruct for u16 {

}

impl ExecStruct for u32 {

}

impl ExecStruct for u64 {

}

impl ExecStruct for usize {

}

impl ExecStruct for u128 {

}

impl ExecStruct for char {

}

impl ExecStruct for bool {

}

#[verifier(external_body)]
pub broadcast proof fn axiom_max_count_size_rel<T>()
    ensures
        spec_nat_pow2(spec_size::<T>()) / 2 < (#[trigger] spec_max_count::<T>()) <= spec_nat_pow2(
            (spec_size::<T>()) * 8,
        ),
{
}

#[verifier(external_body)]
pub broadcast proof fn axiom_set_full_max_count_rel<T>()
    ensures
        Set::<T>::full().len() == #[trigger] spec_max_count::<T>(),
{
}

// All executable types should have a size and its set should be finite.
/*#[verifier(external_body)]
    pub broadcast proof fn axiom_exe_set_finite<T>(s: Set<T>)
    ensures
        s.finite()
    {}*/

// Size is undef for types without VTypeCast
// Size == spec_size_def if it has VTypeCast
#[verifier(external_body)]
pub broadcast proof fn axiom_size_from_cast_bytes<T: SpecSize>()
    ensures
        (#[trigger] spec_size::<T>()) == T::spec_size_def(),
{
}

#[verifier(external_body)]
pub broadcast proof fn axiom_size_from_cast_bytes_def<T: SpecSize + VTypeCast<Seq<u8>>>(val: T)
    ensures
        T::spec_size_def() == VTypeCast::<Seq<u8>>::vspec_cast_to(val).len(),
{
}

/*impl<T: VTypeCast<Seq<u8>>> SpecSize for T {
        open spec fn spec_size_def() -> nat
        {
            let x: Self = arbitrary();
            let s: Seq<u8> = x.vspec_cast_to();
            s.len()
        }
    }*/
} // verus!
impl_spec_size_for_basic! {[usize, 8], [u128, 16], [u64, 8], [u32, 4], [u16, 2], [u8, 1], [bool, 1], [char, 1], [(), 0]}

verus! {

impl<T> SpecSize for Ghost<T> {
    #[verifier(inline)]
    open spec fn spec_size_def() -> nat {
        0
    }
}

impl<T> SpecSize for Tracked<T> {
    #[verifier(inline)]
    open spec fn spec_size_def() -> nat {
        0
    }
}

impl<T: SpecSize, M> SpecSize for SecType<T, M> {
    #[verifier(inline)]
    open spec fn spec_size_def() -> nat {
        T::spec_size_def()
    }
}

impl<T> SpecSize for Option<T> {
    closed spec fn spec_size_def() -> nat;
}

} // verus!
verus! {

pub proof fn proof_bytes_len(data: u64, s: Seq<u8>)
    requires
        s =~~= data.vspec_cast_to(),
    ensures
        s.len() == 8,
{
}

pub proof fn proof_bytes_len4(data: u32, s: Seq<u8>)
    requires
        s =~~= data.vspec_cast_to(),
    ensures
        s.len() == 4,
{
}

pub proof fn proof_bytes_len2(data: u16, s: Seq<u8>)
    requires
        s =~~= data.vspec_cast_to(),
    ensures
        s.len() == 2,
{
}

pub proof fn proof_bytes_len1(data: u8, s: Seq<u8>)
    requires
        s =~~= data.vspec_cast_to(),
    ensures
        s.len() == 1,
{
}

pub proof fn proof_bytes_len0(data: usize, s: Seq<u8>)
    requires
        s =~~= data.vspec_cast_to(),
    ensures
        s.len() == 8,
{
}

} // verus!
