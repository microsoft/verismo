use super::*;
verus! {
    pub trait SpecDefault {
        spec fn spec_default() -> Self where Self: core::marker::Sized;
    }

    pub open spec fn spec_default_<T: SpecDefault>() -> T {
        <T as SpecDefault>::spec_default()
    }

    impl SpecDefault for () {
        open spec fn spec_default() -> Self;
    }

    impl<T> SpecDefault for Ghost<T> {
        open spec fn spec_default() -> Self {
            arbitrary()
        }
    }

    impl<T> SpecDefault for Tracked<T> {
        open spec fn spec_default() -> Self {
            arbitrary()
        }
    }
}

macro_rules! impl_typecast_to_bytes_traits {
    ($($baset: ty),*$(,)*) => {
        $(verus!{
            impl SpecDefault for $baset {
                open spec fn spec_default() -> Self {
                    0 as $baset
                }
            }
        })*
    }
}

impl_typecast_to_bytes_traits! {u64, u32, u16, u8, usize, int, nat}
