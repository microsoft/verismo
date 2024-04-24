use super::*;
use crate::tspec_e::SecSeqByte;
verus! {

pub trait VTypeCast<T> {
    // verus macro transform a as int to vspec_cast_to::<_, int>(a)
    spec fn vspec_cast_to(self) -> T where Self: core::marker::Sized;
}

pub trait SpecInto<T> {
    spec fn spec_into(self) -> T where Self: core::marker::Sized;
}

pub open spec fn is_castable<T1: IsConstant + SpecSize, T2: IsConstant + SpecSize>(t1: T1) -> bool {
    &&& spec_size::<T1>() == spec_size::<
        T2,
    >()/*&&& exists |t2: T2|
            t1.is_constant_to(1) == t2.is_constant_to(1)
            && t1.is_constant_to(2) == t2.is_constant_to(2)
            && t1.is_constant_to(3) == t2.is_constant_to(3)
            && t1.is_constant_to(4) == t2.is_constant_to(4)*/

}

impl<T2, T1: VTypeCast<T2>> SpecInto<T2> for T1 {
    open spec fn spec_into(self) -> T2 {
        self.vspec_cast_to()
    }
}

#[verifier(external_body)]
pub broadcast proof fn axiom_cast_to_seq_unique<T: VTypeCast<SecSeqByte>>(val: T)
    ensures
        val === VTypeCast::<SecSeqByte>::vspec_cast_to(val).vspec_cast_to(),
{
}

#[verifier(external_body)]
broadcast prooffn axiom_into_conversion_bytes<T1: VTypeCast<SecSeqByte> + IsConstant>(b: SecSeqByte)
    ensures
        VTypeCast::<T1>::vspec_cast_to(b).vspec_cast_to() =~~= b,
{
}

pub proof fn proof_cast_from_seq_unique<T: VTypeCast<SecSeqByte>>(val: T)
    ensures
        val === VTypeCast::<SecSeqByte>::vspec_cast_to(val).vspec_cast_to(),
{
}

#[verifier(opaque)]
pub open spec fn field_at<T: VTypeCast<SecSeqByte>, F: VTypeCast<SecSeqByte>>(
    val: T,
    offset: nat,
) -> F {
    let bytes: SecSeqByte = val.vspec_cast_to();
    let b = bytes.subrange(offset as int, (offset + spec_size::<F>()) as int);
    b.vspec_cast_to()
}

#[verifier(opaque)]
pub open spec fn field_set<T: VTypeCast<SecSeqByte>, F: VTypeCast<SecSeqByte>>(
    prev_val: T,
    val: T,
    offset: nat,
    f: F,
) -> bool {
    let prev_bytes: SecSeqByte = prev_val.vspec_cast_to();
    let bytes: SecSeqByte = val.vspec_cast_to();
    bytes =~~= prev_bytes.take(offset as int) + f.vspec_cast_to() + prev_bytes.skip(
        (offset + spec_size::<F>()) as int,
    )
}

pub proof fn proof_field_set_at<
    T: SpecSize + IsConstant + VTypeCast<SecSeqByte>,
    F: SpecSize + IsConstant + VTypeCast<SecSeqByte>,
>(prev_val: T, val: T, offset: nat, f: F)
    requires
        offset < spec_size::<T>(),
        field_set(prev_val, val, offset, f),
    ensures
        field_at(val, offset) === f,
{
    reveal(field_set);
    reveal(field_at);
    proof_cast_from_seq_unique(f);
    let prev_bytes: SecSeqByte = prev_val.vspec_cast_to();
    let bytes: SecSeqByte = val.vspec_cast_to();
    let fb: SecSeqByte = f.vspec_cast_to();
    let bytes = (prev_bytes.take(offset as int) + fb + prev_bytes.skip(
        (offset + spec_size::<F>()) as int,
    ));
    assert(bytes.subrange(offset as int, (offset + spec_size::<F>()) as int) =~~= fb);
}

pub broadcast proof fn proof_field_set_constant<
    T: SpecSize + IsConstant + VTypeCast<SecSeqByte>,
    F: SpecSize + IsConstant + VTypeCast<SecSeqByte>,
>(prev_val: T, val: T, offset: nat, f: F)
    requires
        offset < spec_size::<T>(),
        f.is_constant(),
        prev_val.is_constant(),
        #[trigger] field_set(prev_val, val, offset, f),
    ensures
        val.is_constant(),
{
    reveal(field_set);
    let bytes: SecSeqByte = val.vspec_cast_to();
    proof_into_is_constant::<_, SecSeqByte>(prev_val);
    proof_into_is_constant::<_, SecSeqByte>(f);
    assert(bytes.is_constant());
    proof_into_is_constant::<_, T>(bytes)
}

pub proof fn proof_into_is_constant<T1: VTypeCast<T2> + IsConstant, T2: IsConstant>(v: T1)
    ensures
        v.is_constant() <==> VTypeCast::<T2>::vspec_cast_to(v).is_constant(),
        v.is_constant_to(1) <==> VTypeCast::<T2>::vspec_cast_to(v).is_constant_to(1),
        v.is_constant_to(2) <==> VTypeCast::<T2>::vspec_cast_to(v).is_constant_to(2),
        v.is_constant_to(3) <==> VTypeCast::<T2>::vspec_cast_to(v).is_constant_to(3),
        v.is_constant_to(4) <==> VTypeCast::<T2>::vspec_cast_to(v).is_constant_to(4),
{
    proof_into_is_constant_to::<T1, T2>(v, 1);
    proof_into_is_constant_to::<T1, T2>(v, 2);
    proof_into_is_constant_to::<T1, T2>(v, 3);
    proof_into_is_constant_to::<T1, T2>(v, 4);
}

#[verifier(external_body)]
pub proof fn proof_into_is_constant_to<T1: VTypeCast<T2> + IsConstant, T2: IsConstant>(
    v: T1,
    vmpl: nat,
)
    requires
        1 <= vmpl <= 4,
    ensures
        v.is_constant_to(vmpl) <==> VTypeCast::<T2>::vspec_cast_to(v).is_constant_to(vmpl),
{
}

pub proof fn proof_subrange_is_constant_to(b: SecSeqByte, start: int, end: int, vmpl: nat)
    requires
        b.is_constant_to(vmpl),
        0 <= start,
        start <= end,
        end <= b.len(),
    ensures
        b.subrange(start, end).is_constant_to(vmpl),
{
}

pub proof fn proof_bytes_add_is_constant_to(b1: SecSeqByte, b2: SecSeqByte, vmpl: nat)
    ensures
        (b1.is_constant_to(vmpl) && b2.is_constant_to(vmpl)) <==> (b1 + b2).is_constant_to(vmpl),
{
    let b = (b1 + b2);
    if (b1.is_constant_to(vmpl) && b2.is_constant_to(vmpl)) {
        assert forall|i| 0 <= i < b.len() implies b[i].is_constant_to(vmpl) by {
            if i < b1.len() {
                assert(b[i] === b1[i]);
            } else {
                assert(b[i] === b2[i - b1.len()]);
            }
        }
    }
    if b.is_constant_to(vmpl) {
        assert(b1 =~~= b.take(b1.len() as int));
        assert(b2 =~~= b.skip(b1.len() as int));
        proof_subrange_is_constant_to(b, 0, b1.len() as int, vmpl);
        proof_subrange_is_constant_to(b, b1.len() as int, b.len() as int, vmpl);
    }
}

pub proof fn proof_bytes_add_is_constant(b1: SecSeqByte, b2: SecSeqByte)
    ensures
        (b1.is_constant() && b2.is_constant()) <==> (b1 + b2).is_constant(),
{
    proof_bytes_add_is_constant_to(b1, b2, 1);
    proof_bytes_add_is_constant_to(b1, b2, 2);
    proof_bytes_add_is_constant_to(b1, b2, 3);
    proof_bytes_add_is_constant_to(b1, b2, 4);
}

pub open spec fn fn_vspec_cast_to<T1: VTypeCast::<T2>, T2>() -> spec_fn(T1) -> T2 {
    |v: T1| VTypeCast::<T2>::vspec_cast_to(v)
}

} // verus!
macro_rules! impl_typecast_trait_single {
    ($lt:ty, [$($rt: ty,)*]) => {
        $(verus!{
            impl VTypeCast<$rt> for $lt {
                open spec fn vspec_cast_to(self) -> $rt {
                    builtin::spec_cast_integer::<$lt, $rt>(self)
                }
            }
        }
)*
    }
}

macro_rules! impl_typecast_traits {
    ($($lt: ty,)*) => {
        $(
        impl_typecast_trait_single!{$lt, [u8, u16, u32, u64, u128, usize, int, nat,]}
        )*
    }
}
macro_rules! impl_typecast_to_bool_traits {
    ($($lt: ty,)*) => {
        paste::paste!{
            $(verus!{
                impl VTypeCast<bool> for $lt {
                    open spec fn vspec_cast_to(self) -> bool {
                        self != 0
                    }
                }

                impl VTypeCast<$lt> for bool {
                    open spec fn vspec_cast_to(self) -> $lt {
                        choose |ret: $lt| self === ret.vspec_cast_to()
                    }
                }
            }
)*
        }
    }
}

macro_rules! impl_typecast_to_bytes_traits {
    ($($lt: ty,)*) => {
        paste::paste!{
        $(verus!{
            impl VTypeCast<Seq<u8>> for $lt {
                open spec fn vspec_cast_to(self) -> Seq<u8> {
                    stream::basic::[<$lt _to_stream>](self)
                }
            }

            impl VTypeCast<$lt> for Seq<u8> {
                open spec fn vspec_cast_to(self) -> $lt {
                    choose |ret: $lt| self === ret.vspec_cast_to()
                }
            }
        }
)*
        }
    }
}

impl_typecast_to_bytes_traits! {u8, u16, u32, u64, u128, usize, char, bool, }

impl_typecast_traits! {u8, u16, u32, u64, u128, usize, int, nat, }

impl_typecast_to_bool_traits! {u8, u16, u32, u64, u128, usize, int, nat, }

impl_typecast_trait_single! {char, [u8,]}

verus! {

impl VTypeCast<Seq<u8>> for () {
    #[verifier(inline)]
    open spec fn vspec_cast_to(self) -> Seq<u8> {
        Seq::empty()
    }
}

impl<T> VTypeCast<Seq<u8>> for Ghost<T> {
    #[verifier(inline)]
    open spec fn vspec_cast_to(self) -> Seq<u8> {
        Seq::empty()
    }
}

impl VTypeCast<Seq<u8>> for Seq<u8> {
    #[verifier(inline)]
    open spec fn vspec_cast_to(self) -> Seq<u8> {
        self
    }
}

impl<T> VTypeCast<Seq<u8>> for Tracked<T> {
    #[verifier(inline)]
    open spec fn vspec_cast_to(self) -> Seq<u8> {
        Seq::empty()
    }
}

} // verus!
