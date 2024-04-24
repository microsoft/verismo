use core::marker::PhantomData;

use super::*;
use crate::tspec::cast::VTypeCast;
use crate::tspec::*;

seq_macro::seq! {N in 1..=4 {
verus! {
    #[verifier::reject_recursive_types(T)]
    #[verifier::reject_recursive_types(M)]
    #[repr(C)]
    pub struct SecType<T, M> {
        val: T,
        view: Ghost<SpecSecType<T, M>>,
    }

    #[is_variant]
    pub enum DataLabel {
        Symbol,
        Unknown,
        TrustedRandom,
        Secret,
    }

    #[verifier::reject_recursive_types(T)]
    #[verifier::reject_recursive_types(M)]
    #[derive(SpecSetter, SpecGetter)]
    pub ghost struct SpecSecType<T, M> {
        pub val: T,
        pub _unused: Option<M>,
        pub valsets: Map<nat, Set<T>>, // vmpl1 -> guess space
        // When force_secret[vmpl] ==> valsets[vmpl]!=1,
        // This is used to ensure upgrade function and downgrade functions.
        // Symbol might be secret or non-secret depending on the valset.
        // Allowed upgrade:
        // others == dependent or concrete
        // TrustedRandom ==> Symbol,
        // Dependent && is_full() ===> Symbol,
        // secret1 + secret2  ==> dependent1,
        // secret1 * secret2  ==> dependent2,
        // unknown + secret2 ==> dependent3,
        // unknown - depenent ==> dependent4,
        // TrustedRandom ==> Concrete,
        // concrete op concrete ==> concrete,
        // concrete op others ==> dep,
        // dependent1 && len() == 1 ==> concrete,
        pub labels: Map<nat, DataLabel>,
    }

    pub trait IsFullSecret {
        spec fn is_fullsecret_to(&self, vmpl: nat) -> bool;
    }

    pub trait IsFullSecretToAll {
        spec fn is_fullsecret(&self) -> bool;
    }

    impl<T: IsFullSecret> IsFullSecretToAll for T {
        open spec fn is_fullsecret(&self) -> bool {
            #(&&& self.is_fullsecret_to(N))*
        }
    }

    impl<T, M> ExecStruct for SecType<T, M> {}
    //impl<T, M> ExecStruct for SpecSecType<T, M>{}

    pub trait SecMemType<T, M> {
        spec fn view(&self) -> SpecSecType<T, M>;
    }

    impl<T, M> SecMemType<T, M> for SecType<T, M> {
        closed spec fn view(&self) -> SpecSecType<T, M> {
            self.view@.spec_set_val(self.val)
        }
    }

    impl<T: core::clone::Clone, M> core::clone::Clone for SecType<T, M> {
        #[verifier(external_body)]
        fn clone(&self) -> (ret: Self)
        ensures *self === ret
        {
            SecType {
                val: self.val.clone(),
                view: Ghost(self@),
            }
        }
    }

    impl<T: core::marker::Copy, M> core::marker::Copy for SecType<T, M> {}

    impl<T, M> SecType<T, M> {
        /// Iff valset is full or the data is a trusted random val.
        pub spec fn spec_new(val: SpecSecType<T, M>) -> Self;

        pub open spec fn call_self(self) -> Self {
            self
        }

        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        pub proof fn axiom_spec_new(val: SpecSecType<T, M>)
        ensures
            (#[trigger]Self::spec_new(val))@ === val,
        {}

        #[verifier(external_body)]
        #[verifier(broadcast_forall)]
        pub proof fn axiom_ext_equal(val: SecType<T, M>, val2: SecType<T, M>)
        ensures
            (val@ === val2@) == (val === val2),
        {}

        #[inline(always)]
        #[verifier(external_body)]
        pub exec fn upgrade_secret(&mut self, Ghost(vmpl): Ghost<nat>)
        requires
            old(self)@.valsets[vmpl] =~~= Set::full() ||
            old(self)@.labels[vmpl].is_TrustedRandom(),
        ensures
            self@ == old(self)@.spec_set_labels(old(self)@.labels.insert(vmpl, DataLabel::Secret)),
        {}

        #[inline(always)]
        #[verifier(external_body)]
        // TODO: enable precondition checking
        // making a unknown data to public to vmpl/hv.
        // Data with other labels cannot become public through this API.
        pub exec fn downgrade_security(&mut self, Ghost(vmpl): Ghost<nat>)
        requires
            old(self).wf_value(),
        ensures
            self@ == old(self)@.spec_set_labels(old(self)@.labels.insert(vmpl, DataLabel::Symbol)),
            self@ == old(self)@.spec_set_valsets(old(self)@.valsets.insert(vmpl, self@.valsets[vmpl])),
            self@.valsets[vmpl].len() == 1,
            self@.valsets[vmpl] =~~= set![self@.val],
            self.wf_value(),
        {}

        pub exec fn declassify(&mut self)
        /*requires
            !old(self)@.labels[1].is_Secret(),
            !old(self)@.labels[2].is_Secret(),
            !old(self)@.labels[3].is_Secret(),
            !old(self)@.labels[4].is_Secret(),*/
        requires
            old(self).wf_value()
        ensures
            self@.labels[1].is_Symbol(),
            self@.labels[2].is_Symbol(),
            self@.labels[3].is_Symbol(),
            self@.labels[4].is_Symbol(),
            self@.is_constant(),
            self@ == old(self)@.spec_set_valsets(self@.valsets).spec_set_labels(self@.labels),
            self.wf_value(),
        {
            self.downgrade_security(Ghost(1));
            self.downgrade_security(Ghost(2));
            self.downgrade_security(Ghost(3));
            self.downgrade_security(Ghost(4));
        }

        #[inline(always)]
        #[verifier(external_body)]
        pub exec fn reveal_value(self) -> (ret: T)
        requires
            self.is_constant(),
        ensures
            self@.val == ret,
        {
            self.val
        }

        pub closed spec fn wf_value(&self) -> bool {
            &&& self@.wf_value()
            &&& self.val === self@.val
        }
    }

    impl<T, M> IsFullSecret for SpecSecType<T, M> {
        open spec fn is_fullsecret_to(&self, vmpl: nat) -> bool {
            self.valsets[vmpl] =~~= Set::full()
        }
    }

    impl<T, M> IsFullSecret for SecType<T, M> {
        open spec fn is_fullsecret_to(&self, vmpl: nat) -> bool {
            self@.is_fullsecret_to(vmpl)
        }
    }

    impl<T, M> IsConstant for SpecSecType<T, M> {
        open spec fn is_constant_to(&self, vmpl: nat) -> bool {
            &&& self.valsets[vmpl].len() == 1
            &&& self.valsets[vmpl] =~~= set![self.val]
            &&& self.labels[vmpl].is_Symbol()
            &&& self.wf_value()
        }
        open spec fn is_constant(&self) -> bool {
            #(
                &&& self.is_constant_to(N)
            )*
        }
    }

    impl<T, M> SpecSecType<T, M> {
        pub proof fn proof_constant(&self)
        requires
            self.is_constant(),
        ensures
            *self === SpecSecType::constant(self.val)
        {
            let expected = SpecSecType::<T, M>::constant(self.val);
            assert(self.valsets =~~= expected.valsets) by {
                assert(expected.valsets.dom() =~~= self.valsets.dom());

                assert forall |vmpl: nat| expected.valsets.contains_key(vmpl)
                implies
                    self.valsets[vmpl] === expected.valsets[vmpl]
                by {
                    assert(0 < vmpl <= 4);
                    assert(self.valsets.contains_key(vmpl));
                    assert(self.valsets[vmpl] =~~= expected.valsets[vmpl]);
                }
            }
            assert(self.labels =~~= expected.labels)by {
                assert(expected.labels.dom() =~~= self.labels.dom());
                assert forall |vmpl: nat|
                    expected.labels.contains_key(vmpl) == self.labels.contains_key(vmpl) by{};
                assert forall |vmpl: nat| expected.labels.contains_key(vmpl)
                implies
                    self.labels[vmpl] === expected.labels[vmpl]
                by {
                    assert(0 < vmpl <= 4);
                    assert(self.labels.contains_key(vmpl));
                    assert(self.labels[vmpl] =~~= expected.labels[vmpl]);
                }
            }
            assert(self.val =~~= expected.val);
        }
    }

    impl<T, M> SecType<T, M> {
        pub proof fn proof_constant_wf(val: T)
        ensures
            SecType::spec_constant(val).wf()
        {}
    }

    impl<T, M> IsConstant for SecType<T, M> {
        #[verifier(inline)]
        open spec fn is_constant_to(&self, vmpl: nat) -> bool {
            &&& self@.is_constant_to(vmpl)
            &&& self.wf_value()
        }

        open spec fn is_constant(&self) -> bool {
           &&& self@.is_constant()
           &&& self.wf_value()
        }
    }

    impl<T, M> SpecSecType<T, M> {
        pub open spec fn call_self(self) -> Self {
            self
        }
        pub open spec fn wf_vmpl(valsets: Map<nat, Set<T>>, labels: Map<nat, DataLabel>, vmpl: nat) -> bool {
            //&&& valsets[vmpl] =~~= Set::full() ==> labels[vmpl].is_Symbol()
            &&& labels[vmpl].is_TrustedRandom() ==> valsets[vmpl] =~~= Set::full()
            &&& labels[vmpl].is_Secret() ==> valsets[vmpl] =~~= Set::full()
            &&& labels.contains_key(vmpl)
            &&& valsets.contains_key(vmpl)
            &&& valsets[vmpl].len() > 0
            &&& valsets[vmpl].finite()
        }

        pub open spec fn wf_value(&self) -> bool {
            #(
                &&& Self::wf_vmpl(self.valsets, self.labels, N)
            )*
            &&& self._unused === None
            &&& self.valsets.dom() =~~= set![1,2,3,4]
            &&& self.labels.dom() =~~= set![1,2,3,4]
        }

        pub open spec fn bop_new<Rhs, T2>(self, rhs: SpecSecType<Rhs, M>, op: spec_fn(T, Rhs) -> T2) -> SpecSecType<T2, M> {
            SpecSecType {
                val: op(self.val, rhs.val),
                _unused: rhs._unused,
                valsets: Map::new(
                    |vmpl| 1 <= vmpl <=4,
                    |vmpl| set_op(self.valsets[vmpl], rhs.valsets[vmpl], op)
                ),
                labels: Map::new(|vmpl| 1 <= vmpl <=4, |vmpl| DataLabel::Symbol)
            }
        }

        pub proof fn proof_bop_new<Rhs, T2>(self, rhs: SpecSecType<Rhs, M>, op: spec_fn(T, Rhs) -> T2) -> (ret: SpecSecType<T2, M>)
        requires
            self.wf_value(),
            rhs.wf_value(),
            //Set::<T2>::full().finite(),
        ensures
            ret === self.bop_new(rhs, op),
            ret.wf_value(),
            self._is_constant() && rhs._is_constant() ==> ret._is_constant(),
        {
            let ret = self.bop_new(rhs, op);
            assert forall |i| 1 <= i <=4
            implies
                ret.valsets[i].len() <= self.valsets[i].len() * rhs.valsets[i].len() &&
                ret.valsets[i].len() >= 1 &&
                ret.valsets[i].finite() &&
                #[trigger] SpecSecType::<T2, M>::wf_vmpl(ret.valsets, ret.labels, i)
            by {
                lemma_setop_len(self.valsets[i], rhs.valsets[i], op);
                assert(ret.valsets[i].len() <= self.valsets[i].len() * rhs.valsets[i].len());
                assert(ret.valsets[i].len() >= 1);
                assert(ret.valsets[i].finite());
                assert(SpecSecType::<T2, M>::wf_vmpl(ret.valsets, ret.labels, i));
                //assert(set_op(self.valsets[i], rhs.valsets[i], op).len() <= 1);
            }
            assert(ret.wf_value());
            if self._is_constant() && rhs._is_constant() {
                assert(ret._is_constant()) by {
                    assert forall |i| 1 <= i <=4
                    implies
                        (#[trigger] ret.valsets[i]).len() == 1
                    by{
                        lemma_setop_len(self.valsets[i], rhs.valsets[i], op);
                        assert(1 * 1 == 1);
                    }
                }
            }
            ret
        }

        pub proof fn proof_uop_valset<T2>(self, op: spec_fn(T) -> T2) -> (ret: SpecSecType<T2, M>)
        requires
            self.wf_value(),
            //Set::<T2>::full().finite(),
        ensures
            ret === self.uop_new(op),
            ret.wf_value(),
            self._is_constant() ==> ret._is_constant(),
        {
            self.proof_bop_new::<T, T2>(SpecSecType::constant(arbitrary()), uop_to_bop(op))
        }

        #[verifier(inline)]
        pub open spec fn uop_new<T2>(self, op: spec_fn(T) -> T2) -> SpecSecType<T2, M> {
            self.bop_new(SpecSecType::constant(arbitrary::<T>()), uop_to_bop(op))
        }

        pub closed spec fn secval_eq_at(&self, rhs: Self, vmpl: nat) -> bool {
            &&& (#[trigger]self.valsets[vmpl]).len() == rhs.valsets[vmpl].len()
        }

        pub open spec fn sec_eq(&self, rhs: Self) -> bool {
            #(
                &&& self.valsets[N].len() == rhs.valsets[N].len()
            )*
        }

        pub open spec fn _is_constant(&self) -> bool
        {
            &&& self.sec_eq(Self::constant(Set::<T>::full().choose()))
        }

        // Create a constant value
        pub open spec fn constant(val: T) -> Self
        {
            SpecSecType {
                val,
                _unused: None,
                valsets: Map::new(
                    |vmpl| 1 <= vmpl <=4,
                    |vmpl| Set::<T>::empty().insert(val),
                ),
                labels: Map::new(
                    |vmpl| 1 <= vmpl <=4,
                    |vmpl| DataLabel::Symbol,
                ),
            }
        }
    }

    impl<T, M> SecType<T, M> {
        #[inline(always)]
        pub const fn constant(val: T) -> (ret: Self)
        ensures
            ret@ === SpecSecType::constant(val),
            ret.is_constant(),
            ret === SecType::spec_constant(val)
        {
            Self {
                val,
                view: Ghost(SpecSecType::constant(val)),
            }
        }

        #[inline(always)]
        pub const fn new(val: T) -> (ret: Self)
        ensures
            ret@ === SpecSecType::constant(val),
            ret.is_constant(),
        {
            Self::constant(val)
        }

        #[verifier(inline)]
        pub open spec fn spec_constant(val: T) -> Self
        {
            Self::spec_new(SpecSecType::constant(val))
        }
    }
}
}
}
#[macro_use]
macro_rules! impl_binary_ops_trait_spec_fn {
    ($trt: tt, $baset: ty, $rhs: ty, $out: ty, $fname: ident, $spec_fn: ident) => {
        paste::paste!{
        verus!{
            impl<M> crate::tspec::ops::[<V $trt>]<SpecSecType<$rhs, M>, SpecSecType<$out, M>> for SpecSecType<$baset, M>{
                open spec fn [<$fname>](self, rhs: SpecSecType<$rhs, M>) -> SpecSecType<$out, M> {
                    self.bop_new(rhs, $spec_fn())
                }
            }

            impl<M> crate::tspec::ops::[<V $trt>]<SecType<$rhs, M>, SecType<$out, M>> for SecType<$baset, M>{
                #[verifier(inline)]
                open spec fn [<$fname>](self, rhs: SecType<$rhs, M>) -> SecType<$out, M> {
                    SecType::spec_new(self@.$fname(rhs@))
                }
            }
        }
        }
    }
}

#[macro_use]
macro_rules! impl_binary_ops_trait {
    ($trt: tt, $baset: ty, $rhs: ty, $out: ty, $fname: ident) => {
        paste::paste! {
            impl_binary_ops_trait_spec_fn!{
                $trt, $baset, $rhs, $out, $fname, [<fn_ $fname _ $baset _ $rhs _ $out>]
            }
        }
    };
}
// pattern for i64, u64, int, nat
#[macro_use]
macro_rules! impl_ord_for_all_types {
    ($baset: ty) => {
        verus! {
            impl<M> IntOrd for SpecSecType<$baset, M>
            {
                #[verifier(inline)]
                open spec fn ord_int(&self) -> int {
                    self.val as int
                }
            }

            impl<M> IntOrd for SecType<$baset, M>
            {
                #[verifier(inline)]
                open spec fn ord_int(&self) -> int {
                    self@.ord_int()
                }
            }
        }
    };
}

#[macro_use]
macro_rules! impl_cmp_ops_for_stype {
    ($baset: ty, $rhs: ty, [$([$fname: ident, $op: tt, $trt: ident]),* $(,)*]) => {
        paste::paste!{verus!{$(
            impl<M> SpecSecType<$baset, M> {
                #[verifier(inline)]
                pub open spec fn [<is_secure_ $fname>](self, other: SpecSecType<$rhs, M>) -> bool {
                    self.sec_eq(other)
                }

                pub proof fn [<lemma_const_is_secure_ $fname>](self, other: SpecSecType<$rhs, M>)
                ensures
                    self.is_constant() && other.is_constant() ==> self.[<is_secure_ $fname>](other),
                {}
            }

            impl<M> vops::$trt<SecType<$rhs, M>> for SecType<$baset, M> {
                #[inline(always)]
                exec fn $fname(&self, rhs: &SecType<$rhs, M>) -> (ret: bool)
                requires
                    self@.sec_eq(rhs@),
                    self.wf_value(),
                    rhs.wf_value(),
                ensures
                    (self@.val $op rhs@.val) == ret,
                {
                    self.val $op rhs.val
                }
            }

            impl<M> vops::$trt<$rhs> for SecType<$baset, M> {
                #[inline(always)]
                exec fn $fname(&self, rhs: &$rhs) -> (ret: bool)
                requires
                    self@.sec_eq(Self::spec_constant(*rhs)@),
                    self.wf_value(),
                ensures
                    (self@.val $op Self::spec_constant(*rhs)@.val) == ret,
                {
                    self.$fname(&Self::constant(*rhs))
                }
            }

            impl<M> SecType<$baset, M> {
                #[inline(always)]
                pub exec fn [<sec_ $fname>](&self, rhs: &SecType<$rhs, M>) -> (ret: SecType<bool, M>)
                requires
                    self.wf_value(),
                    rhs.wf_value(),
                ensures
                    ret@ === self@.bop_new(rhs@, |val1: $baset, val2: $rhs| val1 $op val2),
                    ret@ === self@.bop_new(rhs@, [<fn_spec_ $fname _ $baset _ $rhs _ bool>]()),
                    ret.wf_value(),
                {
                    proof {
                        self@.proof_bop_new(rhs@, [<fn_spec_ $fname _ $baset _ $rhs _ bool>]());
                    }
                    SecType {
                        val: self.val $op rhs.val,
                        view: Ghost(self@.bop_new(rhs@, [<fn_spec_ $fname _ $baset _ $rhs _ bool>]()))
                    }
                }
            }
        )*}}
    }
}

#[macro_use]
macro_rules! impl_exe_bops_for_stype {
    ($baset: ty, [$([$fname: ident, $op: tt, $trt: ident, $specout: ty, ($check:tt $val: expr), $use_cast: ident]),* $(,)*]) => {
        paste::paste!{verus!{$(
            impl<M> SecType<$baset, M> {
                #[inline(always)]
                fn [<_ $fname>](self, other: Self) -> (ret: Self)
                requires
                    self.wf_value(),
                    (self@.val $op other@.val) as $baset == self@.val $op other@.val,
                    other@.val $check $val,
                ensures
                    ret@ === (self@ $op other@).$use_cast(),
                    (self $op other)@ === (self@ $op other@),
                    ret@.val == self@.val $op other@.val,
                    //ret@ === (self $op other)@.vspec_cast_to(),
                {
                    proof {
                        assert(VTypeCast::<SpecSecType<$baset, M>>::vspec_cast_to((self $op other)@) ===
                        VTypeCast::<SpecSecType<$baset, M>>::vspec_cast_to(self@ $op other@)) by {
                            assert(self $op other === SecType::spec_new(self@ $op other@));
                            let v1 = (self $op other)@;
                            let v2 = self@ $op other@;
                            assert(v1 === v2);
                        }
                    }
                    let ghost view: SpecSecType<$baset, M> = (self@ $op other@).$use_cast();
                    SecType {
                        val: self.val $op other.val,
                        view: Ghost(view),
                    }
                }
            }

            impl<M> core::ops::$trt<SecType<$baset, M>> for SecType<$baset, M> {
                type Output = Self;
                #[inline(always)]
                exec fn $fname(self, other: Self) -> (ret: Self)
                requires
                    self.wf_value(),
                    other.wf_value(),
                    (self@.val $op other@.val) as $baset == self@.val $op other@.val,
                    other@.val $check $val
                ensures
                    ret@ === (self@ $op other@).$use_cast(),
                    ret@.val == self@.val $op other@.val,
                    (self.is_constant() && other.is_constant()) ==> ret.is_constant(),
                    ret.wf_value(),
                {
                    proof {
                        self@.proof_bop_new(other@, [<fn_spec_ $fname _ $baset _ $baset _ $specout>]());
                        let ret: SpecSecType<$baset, M> = (self@ $op other@).proof_uop_valset(fn_vspec_cast_to());
                    }
                    self.[<_ $fname>](other)
                }
            }

            impl<M> core::ops::[<$trt Assign>]<SecType<$baset, M>> for SecType<$baset, M> {
                fn [<$fname _assign>](&mut self, other: SecType<$baset, M>)
                requires
                    old(self).wf_value(),
                    other.wf_value(),
                    (old(self)@.val $op other@.val) as $baset == old(self)@.val $op other@.val,
                    other@.val $check $val
                ensures
                    (old(self) $op other)@.$use_cast() === self@,
                    (old(self).is_constant() && other.is_constant()) ==> self.is_constant(),
                    self.wf_value(),
                {
                    *self = core::ops::$trt::<SecType<$baset, M>>::$fname(*self, other);
                }
            }

            impl<M> core::ops::$trt<SecType<$baset, M>> for $baset {
                type Output = Self;
                #[inline(always)]
                exec fn $fname(self, other: SecType<$baset, M>) -> (ret: Self)
                requires
                    other.wf_value(),
                    other.is_constant(),
                    (self $op other@.val) as $baset == self $op other@.val,
                    other@.val $check $val
                ensures
                    ret == self $op other@.val
                {
                    SecType::constant(self).$fname(other).reveal_value()
                }
            }

            impl<M> core::ops::$trt<$baset> for SecType<$baset, M> {
                type Output = Self;
                #[inline(always)]
                exec fn $fname(self, other: $baset) -> (ret: Self)
                requires
                    self.wf_value(),
                    (self@.val $op other) as $baset == self@.val $op other,
                    other $check $val
                ensures
                    (self@ $op SpecSecType::constant(other)).$use_cast() === ret@,
                    (self.is_constant()) ==> ret.is_constant(),
                    ret.wf_value(),
                {
                    self.$fname(Self::constant(other))
                }
            }
        )*

        }}
    };
}

#[macro_use]
macro_rules! impl_exe_not_for_stype {
    ($baset: ty, [$([$fname: ident, $op: tt, $trt: ident]),* $(,)*]) => {
        paste::paste!{
        verus!{
        $(impl<M> crate::tspec::ops::[<VSpec $trt>] for SpecSecType<$baset, M> {
            open spec fn [<spec_ $fname>](self) -> Self {
                self.uop_new(fnspec::[<fn_spec_ $fname _ $baset _ $baset>]())
            }
        }

        impl<M> crate::tspec::ops::[<VSpec $trt>] for SecType<$baset, M> {
            #[verifier(inline)]
            open spec fn [<spec_ $fname>](self) -> SecType<$baset, M> {
                SecType::spec_new(self@.[<spec_ $fname>]())
            }
        }

        impl<M> [<V $trt>] for SecType<$baset, M> {
            type Output = SecType<$baset, M>;
            open spec fn [<requires_ $fname>](self) -> bool {
                self.wf_value()
            }

            open spec fn [<ensures_ $fname>](self, ret: Self) -> bool {
                &&& ret@  === self@.[<spec_ $fname>]()
                &&& self.is_constant() ==> ret.is_constant()
                &&& ret.wf_value()
            }

            #[inline(always)]
            exec fn $fname(self) -> (ret: Self)
            {
                proof {
                    (self@).proof_uop_valset([<fn_spec_ $fname _ $baset _ $baset>]());
                }
                self.[<_ $fname>]()
            }
        }

        impl<M> SecType<$baset, M> {
            #[inline(always)]
            exec fn [<_ $fname>](self) -> (ret: Self)
            ensures
                ret@ === self@.[<spec_ $fname>](),
            {
                Self {
                    val: $op self.val,
                    view: Ghost(self@.[<spec_ $fname>]()),
                }
            }
        }
        )*
        }}
    };
}

#[macro_export]
macro_rules! impl_exe_cast_to_sectype {
    ($baset: ty, [$($out: ty),*$(,)*]) => {
    verus!{
        impl<M> core::convert::Into<$baset> for SecType<$baset, M> {
            // Required method
            //#[verifier(external_body)]
            fn into(self) -> (ret: $baset)
            requires
                self.wf_value(),
                self.is_constant(),
            ensures
                ret == self@.val,
                ret === self.vspec_cast_to(),
            {
                self.val as $baset
            }
        }
        $(impl<M> core::convert::Into<SecType<$out, M>> for SecType<$baset, M> {
            // Required method
            #[verifier(external_body)]
            fn into(self) -> (ret: SecType<$out, M>)
            requires
                self.wf_value(),
            ensures
                ret === self.vspec_cast_to(),
                ret@ === self@.vspec_cast_to(),
                ret.wf_value(),
                self.is_constant() ==> ret.is_constant()
            {
                SecType{
                    val: self.val as $out,
                    view: Ghost(self@.vspec_cast_to()),
                }
            }
        }

        impl<M> core::convert::Into<$out> for SecType<$baset, M> {
            // Required method
            fn into(self) -> (ret: $out)
            requires
                self.wf_value(),
                self.is_constant(),
            ensures
                ret == self@.val as $out,
            {
                self.val as $out
            }
        }
        impl<M> core::convert::Into<SecType<$out, M>> for $baset {
            // Required method
            fn into(self) -> (ret: SecType<$out, M>)
            ensures
                ret === self.vspec_cast_to(),
                ret@ == SpecSecType::<$out, M>::constant(self as $out),
                ret.is_constant(),
            {
                SecType{
                    val: self as $out,
                    view: Ghost(SpecSecType::constant(self as $out)),
                }
            }
        }
    )*

    impl<M> core::convert::Into<SecType<$baset, M>> for $baset {
        // Required method
        fn into(self) -> (ret: SecType<$baset, M>)
        requires
            self.wf()
        ensures
            ret === self.vspec_cast_to(),
            ret@ === SpecSecType::<$baset, M>::constant(self),
            ret.is_constant(),
        {
            SecType{
                val: self,
                view: Ghost(SpecSecType::constant(self)),
            }
        }
    }
    }
    }
}

#[macro_export]
macro_rules! impl_exe_default {
    ($($baset: ty),*$(,)*) => {
    $(verus!{
    impl<M> Default for SecType<$baset, M>  {
        fn default() -> (ret: Self)
        ensures
            ret@ == SpecSecType::<$baset, M>::spec_default(),
            ret.is_constant(),
        {
            Self::constant(0)
        }
    }

    impl<M> SpecDefault for SpecSecType<$baset, M>  {
        #[verifier(inline)]
        open spec fn spec_default() -> Self {
            Self::constant(0)
        }
    }

    impl<M> SpecDefault for SecType<$baset, M>  {
        #[verifier(inline)]
        open spec fn spec_default() -> Self {
            Self::spec_constant(0)
        }
    }
    })*
    }
}

verus! {
    impl<T1: VTypeCast<T2>, T2, M> VTypeCast<SpecSecType<T2, M>> for SpecSecType<T1, M> {
        open spec fn vspec_cast_to(self) -> SpecSecType<T2, M> {
            self.uop_new(fn_vspec_cast_to())
        }
    }

    impl<T1: VTypeCast<T2>, T2, M> VTypeCast<SecType<T2, M>> for SecType<T1, M> {
        #[verifier(inline)]
        open spec fn vspec_cast_to(self) -> SecType<T2, M> {
            SecType::spec_new(self@.vspec_cast_to())
        }
    }
}

#[macro_export]
macro_rules! impl_cast_to_sectype {
    ($baset: ty, $out: ty) => {
        verus! {
            impl<M> VTypeCast<SpecSecType<$out, M>> for $baset {
                #[verifier(inline)]
                open spec fn vspec_cast_to(self) -> SpecSecType<$out, M> {
                    SpecSecType::constant(self.vspec_cast_to())
                }
            }

            impl<M> VTypeCast<SecType<$out, M>> for $baset {
                #[verifier(inline)]
                open spec fn vspec_cast_to(self) -> SecType<$out, M> {
                    SecType::spec_new(self.vspec_cast_to())
                }
            }
        }
    };
}

#[macro_export]
macro_rules! impl_cast_to_basics {
    ($baset: ty, $out: ty) => {
        verus! {
            impl<M> VTypeCast<$out> for SecType<$baset, M> {
                #[verifier(inline)]
                open spec fn vspec_cast_to(self) -> $out {
                    self@.vspec_cast_to()
                }
            }

            impl<M> VTypeCast<$out> for SpecSecType<$baset, M> {
                #[verifier(inline)]
                open spec fn vspec_cast_to(self) -> $out {
                    VTypeCast::<$out>::vspec_cast_to(self.val)
                }
            }
        }
    };
}

#[macro_export]
macro_rules! impl_cast_to {
    ($fromty: ty, [$($out: ty),*$(,)?]) => {
        $(
            impl_cast_to_basics!($fromty, $out);
            impl_cast_to_sectype!($fromty, $out);
        )*
    }
}

#[macro_export]
macro_rules! impl_exe_ops_for_stype {
    ($($baset: ty),* $(,)?) => {
        $(
            impl_cmp_ops_for_stype!($baset, $baset, [[gt, >, VGt], [lt, <, VLt], [le, <=, VLe], [ge, >=, VGe], [eq, ==, VEq]]);
            impl_exe_bops_for_stype!($baset,
                [
                    [add, +, Add, int, (>= 0), vspec_cast_to],
                    [sub, -, Sub, int, (>= 0), vspec_cast_to],
                    [mul, *, Mul, int, (>= 0), vspec_cast_to],
                    [div, /, Div, $baset, (!= 0), call_self],
                    [rem, %, Rem, $baset, (!= 0), call_self],
                    [shr, >>, Shr, $baset, (< (8 * spec_size::<$baset>())), call_self],
                    [shl, <<, Shl, $baset, (< (8 * spec_size::<$baset>())), call_self],
                    [bitxor, ^, BitXor, $baset, (>= 0), call_self],
                    [bitor, |, BitOr, $baset, (>= 0), call_self],
                    [bitand, &, BitAnd, $baset, (>= 0), call_self]
                ]);
            impl_exe_not_for_stype!($baset, [[not, !, Not]]);
        )*
    }
}

#[macro_export]
macro_rules! impl_spec_ops_for_stype {
    ($($baset: ty),*$(,)?) =>
    {
        $(
        impl_ord_for_all_types!($baset);
        impl_cast_to!($baset, [int, nat, usize, u64, u32, u16, u8, Seq<u8>]);
        impl_binary_ops_trait!(SpecAdd, $baset, $baset, int, spec_add);
        impl_binary_ops_trait!(SpecSub, $baset, $baset, int, spec_sub);
        impl_binary_ops_trait!(SpecMul, $baset, $baset, int, spec_mul);
        impl_binary_ops_trait!(SpecBitOr, $baset, $baset, $baset, spec_bitor);
        impl_binary_ops_trait!(SpecBitAnd, $baset, $baset, $baset, spec_bitand);
        impl_binary_ops_trait!(SpecBitXor, $baset, $baset, $baset, spec_bitxor);
        impl_binary_ops_trait!(SpecEuclideanDiv, $baset, $baset, $baset, spec_euclidean_div);
        impl_binary_ops_trait!(SpecEuclideanMod, $baset, $baset, $baset, spec_euclidean_mod);
        impl_binary_ops_trait!(SpecShl, $baset, $baset, $baset, spec_shl);
        impl_binary_ops_trait!(SpecShr, $baset, $baset, $baset, spec_shr);
        )*
    }
}

#[macro_export]
macro_rules! impl_spec_ops_for_seq {
    ($($baset: ty),*$(,)?) =>
    {
        $(
        //impl_cast_to!($baset, [usize, u64, u32, u16, u8, Seq<u8>]);
        impl_binary_ops_trait_spec_fn!(SpecAdd, $baset, $baset, $baset, spec_add, fn_spec_add_seq);
        )*
    }
}

// Pattern for nat
#[macro_export]
macro_rules! impl_ops_for_snat {
    ($($baset: ty,)*) =>
    {
        $(
        impl_ord_for_all_types!($baset);
        impl_cast_to!($baset, [int, nat, usize, u64, u32, u16, u8]);
        impl_binary_ops_trait!(SpecAdd, $baset, $baset, nat, spec_add);
        impl_binary_ops_trait!(SpecSub, $baset, $baset, int, spec_sub);
        impl_binary_ops_trait!(SpecMul, $baset, $baset, nat, spec_mul);
        impl_binary_ops_trait!(SpecEuclideanDiv, $baset, $baset, $baset, spec_euclidean_div);
        impl_binary_ops_trait!(SpecEuclideanMod, $baset, $baset, $baset, spec_euclidean_mod);
        )*
    }
}

// Pattern for sint
#[macro_export]
macro_rules! impl_ops_for_sint {
    ($($baset: ty,)*) =>
    {
        $(
        impl_ord_for_all_types!($baset);
        impl_cast_to!($baset, [int, nat, usize, u64, u32, u16, u8]);
        impl_binary_ops_trait!(SpecAdd, $baset, $baset, int, spec_add);
        impl_binary_ops_trait!(SpecSub, $baset, $baset, int, spec_sub);
        impl_binary_ops_trait!(SpecMul, $baset, $baset, int, spec_mul);
        impl_binary_ops_trait!(SpecEuclideanDiv, $baset, $baset, $baset, spec_euclidean_div);
        impl_binary_ops_trait!(SpecEuclideanMod, $baset, $baset, $baset, spec_euclidean_mod);
        )*
    }
}

/// verismo macro will replace basic types to secure types.
/// Using type alias ensures the macro will not replace the type.
#[macro_export]
macro_rules! impl_secure_type {
    ($memattr: ty, $($p: tt)*) =>
    {
        $($p )* u64_s = SecType<u64, $memattr>;
        $($p )* u32_s = SecType<u32, $memattr>;
        $($p )* u16_s = SecType<u16, $memattr>;
        $($p )* u8_s = SecType<u8, $memattr>;
        $($p )* usize_s = SecType<usize, $memattr>;
        $($p )* int_s = SecType<int, $memattr>;
        $($p )* nat_s = SecType<nat, $memattr>;
        $($p )* bool_s = SecType<bool, $memattr>;
        //$($p )* SecSeqByte = SecType<Seq<u8>, $memattr>;
        $($p )* SecSeqByte = Seq<SpecSecType<u8, $memattr>>;

        $($p )* u64_t = u64;
        $($p )* u32_t = u32;
        $($p )* u16_t = u16;
        $($p )* u8_t = u8;
        $($p )* usize_t = usize;
        $($p )* int_t = int;
        $($p )* nat_t = nat;
        $($p )* bool_t = bool;
    }
}

verus! {
    impl<T> SecType<T, ()> {
        pub open spec fn wf(&self) -> bool {
            self.wf_value()
        }
    }
}

impl_exe_cast_to_sectype!(u64, [usize, u32, u16, u8]);
impl_exe_cast_to_sectype!(u32, [usize, u64, u16, u8]);
impl_exe_cast_to_sectype!(u16, [usize, u64, u32, u8]);
impl_exe_cast_to_sectype!(u8, [usize, u64, u32, u16]);
impl_exe_cast_to_sectype!(usize, [u64, u32, u16, u8]);
impl_exe_default!(u8, u16, u32, u64, usize);
impl_exe_ops_for_stype! {u8, u16, u32, u64, usize}
impl_exe_not_for_stype!(bool, [[not, !, Not]]);
impl_spec_ops_for_stype! {u8, u16, u32, u64, usize}

impl_ops_for_snat! {nat,}
impl_ops_for_sint! {int,}

verus! {
    pub trait VNot {
        type Output;
        spec fn requires_not(self) -> bool where Self: core::marker::Sized;
        spec fn ensures_not(self, ret: Self::Output) -> bool where Self: core::marker::Sized;
        fn not(self) -> (ret: Self::Output) where Self: core::marker::Sized
        requires
            self.requires_not(),
        ensures
            self.ensures_not(ret);
    }

    impl VNot for bool {
        type Output = bool;
        open spec fn requires_not(self) -> bool {
            true
        }

        open spec fn ensures_not(self, ret: bool) -> bool {
            self == !ret
        }

        fn not(self) -> bool {
            !self
        }
    }
}
//impl_spec_ops_for_seq! {Seq<u8>}
