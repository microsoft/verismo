use super::*;

verus! {

// Implement Int Value only for a ghost type without width.
pub trait IntValue {
    spec fn as_int(&self) -> int;

    spec fn from_int(val: int) -> Self where Self: core::marker::Sized;
}

pub trait IntOrd {
    spec fn ord_int(&self) -> int;
}

pub trait NotPrimitive {

}

pub trait ToSetTrait {
    spec fn to_set(&self) -> Set<int>;

    fn contains(&self, sval: u64) -> (ret: bool)
        ensures
            self.to_set().contains(sval as int) == ret,
    ;
}

} // verus!
verus! {

impl<T1: IntValue> VSpecAdd<int, T1> for T1 {
    open spec fn spec_add(self, rhs: int) -> T1 {
        T1::from_int(self.as_int() + rhs)
    }
}

impl<T1: IntValue> VSpecSub<int, T1> for T1 {
    open spec fn spec_sub(self, rhs: int) -> T1 {
        T1::from_int(self.as_int() - rhs)
    }
}

impl<T1: IntValue> VSpecSub<T1, int> for T1 {
    open spec fn spec_sub(self, rhs: T1) -> int {
        self.as_int() - rhs.as_int()
    }
}

impl<T1: IntValue> VSpecEuclideanDiv<int, T1> for T1 {
    open spec fn spec_euclidean_div(self, rhs: int) -> T1 {
        T1::from_int(self.as_int() / rhs)
    }
}

impl<T1: IntValue> VSpecEuclideanMod<int, T1> for T1 {
    open spec fn spec_euclidean_mod(self, rhs: int) -> T1 {
        T1::from_int(self.as_int() % rhs)
    }
}

impl<T1: IntValue> VSpecMul<int, T1> for T1 {
    open spec fn spec_mul(self, rhs: int) -> T1 {
        T1::from_int(self.as_int() * rhs)
    }
}

} // verus!
/*
macro_rules! impl_ordint_for_basic_inner {
    ($itype: ty) => {
        verus! {
            impl IntOrd for $itype {
                #[verifier(inline)]
                open spec fn ord_int(&self) -> int {
                    *self as int
                }
            }
        }
    }
}

macro_rules! impl_ordint_for_basic {
    ($($itype: ty),* $(,)?) => {
        $(
            impl_ordint_for_basic_inner!($itype);
        )*
    }
}
*/
macro_rules! impl_cmp_with_basic {
    ($basict: ty, $($fname: ident),* $(,)?) => {
        paste::paste! {
                                                                verus! {
        impl<T: IntOrd> VSpecOrd<$basict> for T {
            $(
            #[verifier(inline)]
            open spec fn [<$fname>](self, rhs: $basict) -> bool {
                builtin::SpecOrd::$fname(self.ord_int(), rhs as int)
            }
            )*
        }
        }
                                                            }
    };
}

macro_rules! impl_spec_eq_with_basic {
    ($basict: ty, $($rhs: ty),* $(,)?) => {
        $(verus!{
        impl VSpecEq<$rhs> for $basict {
            #[verifier(inline)]
            open spec fn spec_eq(self, rhs: $rhs) -> bool {
                builtin::spec_eq(self, rhs)
            }
        }
        }
)*
        verus!{
        impl<T: IntOrd> VSpecEq<$basict> for T {
            #[verifier(inline)]
            open spec fn spec_eq(self, rhs: $basict) -> bool {
                builtin::spec_eq(self.ord_int(), rhs as int)
            }
        }}
    }
}

macro_rules! impl_spec_eq_with_basics {
    ($($basict: ty),* $(,)?) => {
        $(
            impl_spec_eq_with_basic!{$basict, u64, u32, u16, u8, usize, int, nat}
        )*
    }
}

macro_rules! impl_cmp_with_basics {
    ($($basict: ty),*$(,)*) => {
        $(
        impl_cmp_with_basic!{$basict, spec_lt, spec_le, spec_gt, spec_ge}
        )*
    }
}

macro_rules! impl_cmp_with_as_int {
    ($($fname: ident),* $(,)?) => {
        paste::paste! {
                                                                verus! {
        impl<T: IntOrd, T2: IntOrd> VSpecOrd<T2> for T {
            $(
            #[verifier(inline)]
            open spec fn [<$fname>](self, rhs: T2) -> bool {
                builtin::SpecOrd::$fname(self.ord_int(), rhs.ord_int())
            }
            )*
        }
        impl<T: IntOrd, T2: IntOrd> VSpecEq<T2> for T {
            #[verifier(inline)]
            open spec fn spec_eq(self, rhs: T2) -> bool {
                builtin::spec_eq(self.ord_int(), rhs.ord_int())
            }
        }
        }
                                                            }
    };
}

impl_cmp_with_as_int! {spec_lt, spec_le, spec_gt, spec_ge}

verus! {

pub proof fn lemma_int_value_ord<T: IntOrd>(t1: T, t2: T)
    ensures
        t1.ord_int() > t2.ord_int() ==> t1 > t2,
{
}

} // verus!
impl_cmp_with_basics! {int, nat, u8, u16, u32, u64, usize}
impl_spec_eq_with_basics! {int, nat, u8, u16, u32, u64, usize}

crate::macro_const! {
    #[macro_export]
    pub const MAXU64: u64  = 0xffff_ffff_ffff_ffffu64;
}

verus! {

impl VSpecEq<()> for () {
    #[verifier(inline)]
    open spec fn spec_eq(self, rhs: Self) -> bool {
        true
    }
}

} // verus!
