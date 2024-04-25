use super::*;

verus! {

pub open spec fn fn_spec_to_seq_index<T: VTypeCast<Seq<u8>>>(i: int) -> spec_fn(T) -> u8 {
    |v: T| VTypeCast::<Seq<u8>>::vspec_cast_to(v).index(i)
}

impl<T: VTypeCast<Seq<u8>>, M> VTypeCast<Seq<SpecSecType<u8, M>>> for SecType<T, M> {
    open spec fn vspec_cast_to(self) -> Seq<SpecSecType<u8, M>> {
        Seq::new(spec_size::<T>(), |i| self@.uop_new(fn_spec_to_seq_index(i)))
    }
}

impl<M> VTypeCast<Seq<SpecSecType<u8, M>>> for () {
    open spec fn vspec_cast_to(self) -> Seq<SpecSecType<u8, M>> {
        Seq::empty()
    }
}

} // verus!
