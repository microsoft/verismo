use super::ops::*;
use super::*;

verus! {

pub open spec fn fn_vspec_lt<T1: VSpecOrd::<T2>, T2>() -> spec_fn(T1, T2) -> bool {
    |v1: T1, v2: T2| VSpecOrd::<T2>::spec_lt(v1, v2)
}

pub open spec fn fn_vspec_le<T1: VSpecOrd<T2>, T2>() -> spec_fn(T1, T2) -> bool {
    |v1: T1, v2: T2| VSpecOrd::<T2>::spec_le(v1, v2)
}

pub open spec fn fn_vspec_gt<T1: VSpecOrd<T2>, T2>() -> spec_fn(T1, T2) -> bool {
    |v1: T1, v2: T2| VSpecOrd::<T2>::spec_gt(v1, v2)
}

pub open spec fn fn_vspec_ge<T1: VSpecOrd<T2>, T2>() -> spec_fn(T1, T2) -> bool {
    |v1: T1, v2: T2| VSpecOrd::<T2>::spec_ge(v1, v2)
}

pub open spec fn fn_vspec_eq<T1: VSpecEq<T2>, T2>() -> spec_fn(T1, T2) -> bool {
    |v1: T1, v2: T2| VSpecEq::<T2>::spec_eq(v1, v2)
}

pub open spec fn fn_vspec_neg<T1: VSpecNeg>() -> spec_fn(T1) -> T1 {
    |v1| VSpecNeg::spec_neg(v1)
}

pub open spec fn fn_vspec_not<T1: VSpecNot>() -> spec_fn(T1) -> T1 {
    |v1| VSpecNot::spec_not(v1)
}

pub open spec fn fn_vspec_add<T1: VSpecAdd<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecAdd::<T2, T3>::spec_add(v1, v2)
}

pub open spec fn fn_vspec_sub<T1: VSpecSub<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecSub::<T2, T3>::spec_sub(v1, v2)
}

pub open spec fn fn_vspec_mul<T1: VSpecMul<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecMul::<T2, T3>::spec_mul(v1, v2)
}

pub open spec fn fn_vspec_div<T1: VSpecEuclideanDiv<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecEuclideanDiv::<T2, T3>::spec_euclidean_div(v1, v2)
}

pub open spec fn fn_vspec_rem<T1: VSpecEuclideanMod<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecEuclideanMod::<T2, T3>::spec_euclidean_mod(v1, v2)
}

pub open spec fn fn_vspec_euclidean_div<T1: VSpecEuclideanDiv<T2, T3>, T2, T3>() -> spec_fn(
    T1,
    T2,
) -> T3 {
    |v1: T1, v2: T2| VSpecEuclideanDiv::<T2, T3>::spec_euclidean_div(v1, v2)
}

pub open spec fn fn_vspec_euclidean_mod<T1: VSpecEuclideanMod::<T2, T3>, T2, T3>() -> spec_fn(
    T1,
    T2,
) -> T3 {
    |v1: T1, v2: T2| VSpecEuclideanMod::<T2, T3>::spec_euclidean_mod(v1, v2)
}

pub open spec fn fn_vspec_bitand<T1: VSpecBitAnd<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecBitAnd::<T2, T3>::spec_bitand(v1, v2)
}

pub open spec fn fn_vspec_bitor<T1: VSpecBitOr<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecBitOr::<T2, T3>::spec_bitor(v1, v2)
}

pub open spec fn fn_vspec_bitxor<T1: VSpecBitXor<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| VSpecBitXor::<T2, T3>::spec_bitxor(v1, v2)
}

pub open spec fn fn_vspec_shr<T1: VSpecShr<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| v1 >> v2
}

pub open spec fn fn_vspec_shl<T1: VSpecShl<T2, T3>, T2, T3>() -> spec_fn(T1, T2) -> T3 {
    |v1: T1, v2: T2| v1 << v2
}

} // verus!
macro_rules! def_builtin_unary_spec_fn {
    ($fname: ident, $op: tt, $t1: ty, $t2: ty) => {
        paste::paste! {verus!{
                    pub open spec fn [<fn_ $fname _ $t1 _ $t2>]() -> spec_fn($t1) -> $t2 {
                        |v1: $t1| $op v1
                    }
                }
}
    };
}

macro_rules! def_builtin_spec_fn {
    ($fname: ident, $op: tt, $t1: ty, $t2: ty, $t3: ty) => {
        paste::paste! {
                                                                                        verus!{
            pub open spec fn [<fn_ $fname _ $t1 _ $t2 _ $t3>]() -> spec_fn($t1, $t2) -> $t3 {
                |v1: $t1, v2: $t2| v1 $op v2
            }
        }
                                                                                    }
    };
}

macro_rules! def_builtin_spec_fns {
    ([$([$fname: ident, $op: tt]),* $(,)*], $t1: ty, $t2: ty, $t3: ty) => {
        $(
            def_builtin_spec_fn!{$fname, $op, $t1, $t2, $t3}
        )*
    };
}

macro_rules! def_builtin_cmp_spec_fns_t1 {
    ([$($t1: ty),*$(,)*], $t2: ty, $t3: ty) => {
        $(
        def_builtin_spec_fns!{[[spec_lt, <], [spec_gt, >], [spec_le, <=], [spec_ge, >=], [spec_eq, ==]], $t1, $t2, $t3}
        )*
    }
}

macro_rules! def_builtin_cmp_spec_fns {
    ($($t2: ty),*$(,)*) => {
        $(
            def_builtin_cmp_spec_fns_t1!{[u128, u64, u32, u16, u8, usize int, nat], $t2, bool}
        )*
    }
}

macro_rules! def_builtin_bop_spec_fns_sized {
    ($($t1: ty),*$(,)*) => {
        $(
        def_builtin_spec_fns!{[
            [spec_add, +], [spec_sub, -], [spec_mul, *]
            ],
            $t1, $t1, int}
        def_builtin_spec_fns!{[
                [spec_euclidean_div, /], [spec_euclidean_mod, %],
                [spec_div, /], [spec_rem, %]
                ],
                $t1, $t1, $t1}
        )*
    }
}

macro_rules! def_builtin_bop_spec_fns_nat {
    () => {
        def_builtin_spec_fns! {[
        [spec_add, +], [spec_mul, *], [spec_euclidean_div, /], [spec_euclidean_mod, %],
        [spec_div, /], [spec_rem, %]
        ],
        nat, nat, nat}
        def_builtin_spec_fns! {[
        [spec_sub, -]
        ],
        nat, nat, int}
    };
}

macro_rules! def_builtin_bit_bop_spec_fns_t1 {
    ($($t1: ty),*$(,)*) => {
        $(
        def_builtin_spec_fns!{[
            [spec_bitand, &], [spec_bitor, |], [spec_bitxor, ^], [spec_shr, >>], [spec_shl, <<],
            ],
            $t1, $t1, $t1}
        )*
    }
}

macro_rules! def_builtin_cmp_spec_fns {
    ($($t2: ty),*$(,)*) => {
        $(
            def_builtin_cmp_spec_fns_t1!{[u128, u64, u32, u16, u8, usize, int, nat], $t2, bool}
        )*
    }
}

macro_rules! def_builtin_not_neg {
    ($($t1: ty),*$(,)*) => {
        $(
        def_builtin_unary_spec_fn!{spec_not, !, $t1, $t1}
        )*
    };
}

def_builtin_cmp_spec_fns! {u128, u64, u32, u16, u8, usize, int, nat}
def_builtin_bop_spec_fns_sized! {u128, u64, u32, u16, u8, usize, int}
def_builtin_bop_spec_fns_nat! {}
def_builtin_not_neg! {u128, u64, u32, u16, u8, usize, bool}
def_builtin_bit_bop_spec_fns_t1! {u128, u64, u32, u16, u8, usize}

verus! {

pub open spec fn fn_spec_add_seq<T>() -> spec_fn(Seq<T>, Seq<T>) -> Seq<T> {
    |v1: Seq<T>, v2: Seq<T>| v1 + v2
}

} // verus!
