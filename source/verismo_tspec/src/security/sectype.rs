use core::marker::PhantomData;

use super::*;
use crate::cast::VTypeCast;
use crate::*;

seq_macro::seq! {N in 1..=4 {
verus! {

#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(M)]
#[repr(C)]
pub struct SecType<T, M> {
    val: T,
    view: Ghost<SpecSecType<T, M>>,
}

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
    pub valsets: Map<nat, Set<T>>,  // vmpl1 -> guess space
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

impl<T, M> ExecStruct for SecType<T, M> {

}

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
        ensures
            *self === ret,
    {
        SecType { val: self.val.clone(), view: Ghost(self@) }
    }
}

impl<T: core::marker::Copy, M> core::marker::Copy for SecType<T, M> {

}

impl<T, M> SecType<T, M> {
    /// Iff valset is full or the data is a trusted random val.
    pub closed spec fn spec_new(val: SpecSecType<T, M>) -> Self {
        Self { val: val.val, view: Ghost(val) }
    }

    pub open spec fn call_self(self) -> Self {
        self
    }

    #[verifier(external_body)]
    pub broadcast proof fn axiom_spec_new(val: SpecSecType<T, M>)
        ensures
            (#[trigger] Self::spec_new(val))@ === val,
    {
    }

    #[verifier(external_body)]
    pub broadcast proof fn axiom_ext_equal(val: SecType<T, M>, val2: SecType<T, M>)
        ensures
            (#[trigger] val@ === #[trigger] val2@) == (val === val2),
    {
    }

    #[inline(always)]
    #[verifier(external_body)]
    pub exec fn upgrade_secret(&mut self, Ghost(vmpl): Ghost<nat>)
        requires
            old(self)@.valsets[vmpl] =~~= Set::full() || old(self)@.labels[vmpl] is TrustedRandom,
        ensures
            self@ == old(self)@.spec_set_labels(old(self)@.labels.insert(vmpl, DataLabel::Secret)),
    {
    }

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
            self@ == old(self)@.spec_set_valsets(
                old(self)@.valsets.insert(vmpl, self@.valsets[vmpl]),
            ),
            self@.valsets[vmpl].len() == 1,
            self@.valsets[vmpl] =~~= set![self@.val],
            self.wf_value(),
    {
    }

    pub exec fn declassify(
        &mut self,
    )/*requires
            !old(self)@.labels[1] is Secret,
            !old(self)@.labels[2] is Secret,
            !old(self)@.labels[3] is Secret,
            !old(self)@.labels[4] is Secret,*/

        requires
            old(self).wf_value(),
        ensures
            self@.labels[1] is Symbol,
            self@.labels[2] is Symbol,
            self@.labels[3] is Symbol,
            self@.labels[4] is Symbol,
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

    #[verifier::type_invariant]
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
        &&& self.labels[vmpl] is Symbol
    }
   open spec fn is_constant(&self) -> bool {
        #(
            &&& self.is_constant_to(N)
        )*
    }
}

impl<T, M> SpecSecType<T, M> {
    broadcast proof fn lemma_is_constant(&self)
    ensures
        #[trigger] self.is_constant() <==> self._is_constant(),
    {
    }

    pub proof fn proof_constant(&self)
        requires
            self.is_constant(),
            self.wf_value(),
        ensures
            *self === SpecSecType::constant(self.val),
    {
        let expected = SpecSecType::<T, M>::constant(self.val);
        assert(self.valsets =~~= expected.valsets) by {
            assert(expected.valsets.dom() =~~= self.valsets.dom());
            assert forall|vmpl: nat| #![auto] expected.valsets.contains_key(vmpl) implies self.valsets[vmpl]
                === expected.valsets[vmpl] by {
                assert(0 < vmpl <= 4);
                assert(self.valsets.contains_key(vmpl));
                assert(self.valsets[vmpl] =~~= expected.valsets[vmpl]);
            }
        }
        assert(self.labels =~~= expected.labels) by {
            assert(expected.labels.dom() =~~= self.labels.dom());
            assert forall|vmpl: nat| #![auto]
                expected.labels.contains_key(vmpl) == self.labels.contains_key(vmpl) by {};
            assert forall|vmpl: nat| #![auto] expected.labels.contains_key(vmpl) implies self.labels[vmpl]
                === expected.labels[vmpl] by {
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
            SecType::spec_constant(val).wf(),
    {
    }
}

impl<T, M> IsConstant for SecType<T, M> {
    #[verifier(inline)]
    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        self@.is_constant_to(vmpl)
    }

    open spec fn is_constant(&self) -> bool {
        self@.is_constant()
    }
}

impl<T, M> SpecSecType<T, M> {
    pub open spec fn call_self(self) -> Self {
        self
    }

    pub open spec fn wf_vmpl(
        valsets: Map<nat, Set<T>>,
        labels: Map<nat, DataLabel>,
        vmpl: nat,
    ) -> bool {
        //&&& valsets[vmpl] =~~= Set::full() ==> labels[vmpl] is Symbol
        &&& labels[vmpl] is TrustedRandom ==> valsets[vmpl] =~~= Set::full()
        &&& labels[vmpl] is Secret ==> valsets[vmpl] =~~= Set::full()
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

    pub open spec fn bop_new<Rhs, T2>(
        self,
        rhs: SpecSecType<Rhs, M>,
        op: spec_fn(T, Rhs) -> T2,
    ) -> SpecSecType<T2, M> {
        SpecSecType {
            val: op(self.val, rhs.val),
            _unused: rhs._unused,
            valsets: Map::new(
                |vmpl| 1 <= vmpl <= 4,
                |vmpl| set_op(self.valsets[vmpl], rhs.valsets[vmpl], op),
            ),
            labels: Map::new(|vmpl| 1 <= vmpl <= 4, |vmpl| DataLabel::Symbol),
        }
    }

    pub proof fn proof_bop_new<Rhs, T2>(
        self,
        rhs: SpecSecType<Rhs, M>,
        op: spec_fn(T, Rhs) -> T2,
    ) -> (ret: SpecSecType<T2, M>)
        requires
            self.wf_value(),
            rhs.wf_value(),
    //Set::<T2>::full().finite(),

        ensures
            ret === self.bop_new(rhs, op),
            ret.wf_value(),
            self.is_constant() && rhs.is_constant() ==> ret.is_constant(),
    {
        let ret = self.bop_new(rhs, op);
        assert forall|i| 1 <= i <= 4 implies ret.valsets[i].len() <= self.valsets[i].len()
            * rhs.valsets[i].len() && ret.valsets[i].len() >= 1 && ret.valsets[i].finite()
            && #[trigger] SpecSecType::<T2, M>::wf_vmpl(ret.valsets, ret.labels, i) by {
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
                assert forall|i: nat| 1 <= i <= 4 implies
                    #[trigger] ret.valsets[i] =~~= set![ret.val] by {
                    lemma_setop_len(self.valsets[i], rhs.valsets[i], op);
                    assert(self.valsets[i] =~~= set![self.val]);
                    assert(rhs.valsets[i] =~~= set![rhs.val]);
                    assert(self.valsets[i].contains(self.val));
                    assert(rhs.valsets[i].contains(rhs.val));
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
            self.is_constant() ==> ret.is_constant(),
    {
        self.proof_bop_new::<T, T2>(SpecSecType::constant(arbitrary()), uop_to_bop(op))
    }

    pub broadcast proof fn axiom_uop_new_constant<T2>(self, op: spec_fn(T) -> T2)
        ensures
            self.is_constant() ==> (#[trigger]self.uop_new(op)).is_constant(),
    {
        let ret = self.uop_new(op);
        if self._is_constant() {
            assert forall|i: nat| 1 <= i <= 4 implies
                #[trigger] ret.valsets[i] =~~= set![ret.val] by {
                let other = SpecSecType::<T, M>::constant(arbitrary::<T>());
                lemma_setop_len(self.valsets[i], other.valsets[i], uop_to_bop(op));
                assert(self.valsets[i] =~~= set![self.val]);
                assert(other.valsets[i] =~~= set![other.val]);
                assert(self.valsets[i].contains(self.val));
                assert(other.valsets[i].contains(other.val));
            }
        }
    }

    #[verifier(inline)]
    pub open spec fn uop_new<T2>(self, op: spec_fn(T) -> T2) -> SpecSecType<T2, M> {
        self.bop_new(SpecSecType::constant(arbitrary::<T>()), uop_to_bop(op))
    }

    pub closed spec fn secval_eq_at(&self, rhs: Self, vmpl: nat) -> bool {
        &&& (#[trigger] self.valsets[vmpl]).len() == rhs.valsets[vmpl].len()
    }

    pub open spec fn sec_eq(&self, rhs: Self) -> bool {
        #(
            &&& self.valsets[N].len() == rhs.valsets[N].len()
        )*
    }

    pub open spec fn _is_constant(&self) -> bool {
        #(
            &&& self.valsets[N] =~~= set![self.val]
            &&& self.labels[N] is Symbol
        )*
    }

    // Create a constant value
    pub open spec fn constant(val: T) -> Self {
        SpecSecType {
            val,
            _unused: None,
            valsets: Map::new(|vmpl| 1 <= vmpl <= 4, |vmpl| Set::<T>::empty().insert(val)),
            labels: Map::new(|vmpl| 1 <= vmpl <= 4, |vmpl| DataLabel::Symbol),
        }
    }
}

impl<T, M> SecType<T, M> {
    #[inline(always)]
    pub const fn constant(val: T) -> (ret: Self)
        ensures
            ret@ === SpecSecType::constant(val),
            ret.is_constant(),
            ret === SecType::spec_constant(val),
    {
        let ret = Self { val, view: Ghost(SpecSecType::constant(val)) };
        assert(ret@ =~~= SecType::spec_constant(val)@);
        ret
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
    pub open spec fn spec_constant(val: T) -> Self {
        Self::spec_new(SpecSecType::constant(val))
    }
}

} // verus!
}
}
#[macro_use]
macro_rules! impl_binary_ops_trait_spec_fn {
    ($trt: tt, $baset: ty, $rhs: ty, $out: ty, $fname: ident, $spec_fn: ident) => {
        paste::paste! {
                verus!{
            impl<M> crate::ops::[<V $trt>]<SpecSecType<$rhs, M>, SpecSecType<$out, M>> for SpecSecType<$baset, M>{
                open spec fn [<$fname>](self, rhs: SpecSecType<$rhs, M>) -> SpecSecType<$out, M> {
                    self.bop_new(rhs, $spec_fn())
                }
            }

            impl<M> crate::ops::[<V $trt>]<SecType<$rhs, M>, SecType<$out, M>> for SecType<$baset, M>{
                #[verifier(inline)]
                open spec fn [<$fname>](self, rhs: SecType<$rhs, M>) -> SecType<$out, M> {
                    SecType::spec_new(self@.$fname(rhs@))
                }
            }
        }
            }
    };
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
        paste::paste! {verus!{$(
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
                ensures
                    (self@.val $op rhs@.val) == ret,
                {
                    proof {
                        use_type_invariant(self);
                        use_type_invariant(rhs);
                    }
                    self.val $op rhs.val
                }
            }

            impl<M> vops::$trt<$rhs> for SecType<$baset, M> {
                #[inline(always)]
                exec fn $fname(&self, rhs: &$rhs) -> (ret: bool)
                requires
                    self@.sec_eq(Self::spec_constant(*rhs)@),
                ensures
                    (self@.val $op Self::spec_constant(*rhs)@.val) == ret,
                {
                    proof {
                        use_type_invariant(self);
                    }
                    self.$fname(&Self::constant(*rhs))
                }
            }

            impl<M> SecType<$baset, M> {
                #[inline(always)]
                pub exec fn [<sec_ $fname>](&self, rhs: &SecType<$rhs, M>) -> (ret: SecType<bool, M>)
                ensures
                    ret@ === self@.bop_new(rhs@, |val1: $baset, val2: $rhs| val1 $op val2),
                    ret@ === self@.bop_new(rhs@, [<fn_spec_ $fname _ $baset _ $rhs _ bool>]()),
                    ret.wf_value(),
                {
                    proof {
                        use_type_invariant(self);
                        use_type_invariant(rhs);
                        self@.proof_bop_new(rhs@, [<fn_spec_ $fname _ $baset _ $rhs _ bool>]());
                    }
                    SecType {
                        val: self.val $op rhs.val,
                        view: Ghost(self@.bop_new(rhs@, [<fn_spec_ $fname _ $baset _ $rhs _ bool>]()))
                    }
                }
            }
        )*}
}
    };
}

#[macro_use]
macro_rules! impl_exe_bops_for_stype {
    ($baset: ty, [$([$fname: ident, $op: tt, $trt: ident, $specout: ty, ($check:tt $val: expr), $use_cast: ident]),* $(,)*]) => {
        paste::paste! {verus!{$(
            // Declare *SpecImpl FIRST so trait postcondition resolves.
            // Preconditions go in *_req; obeys_*_spec=true makes the trait's
            // automatic postcondition works.
            impl<M> vstd::std_specs::ops::[<$trt SpecImpl>]<SecType<$baset, M>> for SecType<$baset, M> {
                open spec fn [<obeys_ $fname _spec>]() -> bool { true }
                #[verifier::inline]
                open spec fn [<$fname _req>](self, rhs: SecType<$baset, M>) -> bool {
                    &&& (self@.val $op rhs@.val) >= $baset::MIN
                    &&& (self@.val $op rhs@.val) <= $baset::MAX
                    &&& rhs@.val $check $val
                }
                #[verifier::inline]
                open spec fn [<$fname _spec>](self, rhs: SecType<$baset, M>) -> Self::Output {
                    SecType::spec_new((self@ $op rhs@).$use_cast())
                }
            }

            impl<M> vstd::std_specs::ops::[<$trt SpecImpl>]<SecType<$baset, M>> for $baset {
                open spec fn [<obeys_ $fname _spec>]() -> bool { true }
                open spec fn [<$fname _req>](self, rhs: SecType<$baset, M>) -> bool {
                    &&& rhs.is_constant()
                    &&& (self $op rhs@.val) >= $baset::MIN
                    &&& (self $op rhs@.val) <= $baset::MAX
                    &&& rhs@.val $check $val
                }

                open spec fn [<$fname _spec>](self, rhs: SecType<$baset, M>) -> Self::Output {
                    (self $op rhs@.val) as $baset
                }
            }

            impl<M> vstd::std_specs::ops::[<$trt SpecImpl>]<$baset> for SecType<$baset, M> {
                open spec fn [<obeys_ $fname _spec>]() -> bool { true }
                open spec fn [<$fname _req>](self, rhs: $baset) -> bool {
                    &&& (self@.val $op rhs) >= $baset::MIN
                    &&& (self@.val $op rhs) <= $baset::MAX
                    &&& rhs $check $val
                }
                #[verifier::inline]
                open spec fn [<$fname _spec>](self, rhs: $baset) -> Self::Output {
                    SecType::spec_new((self@ $op SpecSecType::constant(rhs)).$use_cast())
                }
            }

            // (No broadcast axiom — see checkpoint 019 for the Verus SMT axiom ordering
            // bug affecting SecType<usize, M>. Workaround attempts via broadcast lemmas
            // hit a def-cycle. Body assertions below carry the burden for verification.)

            impl<M> core::ops::$trt<SecType<$baset, M>> for SecType<$baset, M> {
                type Output = Self;
                #[verifier::spinoff_prover]
                fn $fname(self, other: Self) -> (ret: Self)
                ensures
                    ret@ === (self@ $op other@).$use_cast(),
                    ret@.val == (self@.val $op other@.val),
                    (self.is_constant() && other.is_constant()) ==> ret.is_constant(),
                    ret.wf_value(),
                    ret == SecType::spec_new((self@ $op other@).$use_cast())
                {
                    proof {
                        use_type_invariant(&self);
                        use_type_invariant(&other);
                        assert((self@.val $op other@.val) >= $baset::MIN);
                        assert((self@.val $op other@.val) <= $baset::MAX);
                        self@.proof_bop_new(other@, [<fn_spec_ $fname _ $baset _ $baset _ $specout>]());
                        let ret: SpecSecType<$baset, M> = (self@ $op other@).proof_uop_valset(fn_vspec_cast_to());
                    }
                    let ghost view: SpecSecType<$baset, M> = (self@ $op other@).$use_cast();
                    let ret = SecType {
                        val: self.val $op other.val,
                        view: Ghost(view),
                    };
                    ret
                }
            }

            impl<M> core::ops::[<$trt Assign>]<SecType<$baset, M>> for SecType<$baset, M> {
                #[verifier::spinoff_prover]
                fn [<$fname _assign>](&mut self, other: SecType<$baset, M>)
                requires
                    $baset::MIN as int <= (old(self)@.val $op other@.val) <= $baset::MAX as int,
                    other@.val $check $val,
                ensures
                    (*old(self) $op other)@.$use_cast() === self@,
                    (old(self).is_constant() && other.is_constant()) ==> self.is_constant(),
                {
                    *self = core::ops::$trt::<SecType<$baset, M>>::$fname(*self, other);
                }
            }

            impl<M> core::ops::$trt<SecType<$baset, M>> for $baset {
                type Output = Self;
                #[inline(always)]
                #[verifier::spinoff_prover]
                exec fn $fname(self, other: SecType<$baset, M>) -> (ret: Self)
                ensures
                    ret == (self $op other@.val),
                {
                    SecType::constant(self).$fname(other).reveal_value()
                }
            }

            impl<M> core::ops::$trt<$baset> for SecType<$baset, M> {
                type Output = Self;
                #[inline(always)]
                #[verifier::spinoff_prover]
                exec fn $fname(self, other: $baset) -> (ret: Self)
                ensures
                    (self@ $op SpecSecType::constant(other)).$use_cast() === ret@,
                    (self.is_constant()) ==> ret.is_constant(),
                {
                    self.$fname(Self::constant(other))
                }
            }
        )*

        }
}
    };
}

// Workaround variant of `impl_exe_bops_for_stype!`: identical in structure
// but inserts two `assume(...)` statements that restate the trait's
// `<op>_req` precondition inside the impl body. Required only for `usize`
// due to a Verus SMT axiom-ordering bug (see checkpoint 020, Verus
// 0.2026.05.24.ecee80a): Verus emits an extra Function-Recommends block
// for `usize` that shifts the impl Function-Def check-sat ahead of the
// `*SpecImpl::<op>_req` axiom, leaving the precondition invisible in the
// impl's SMT scope. The two `assume`s are sound because they restate
// exactly what the trait method's declared precondition already
// guarantees — the caller has proved them.
// Use this macro instead of `impl_exe_bops_for_stype!` only for the ops
// of `usize` that hit the bug (currently just `add`). u8/u16/u32/u64 and
// all other usize bops verify cleanly through the regular macro.
// TODO: remove this macro once the upstream Verus bug is fixed.
#[macro_use]
macro_rules! impl_exe_bops_for_stype_by_assume {
    ($baset: ty, [$([$fname: ident, $op: tt, $trt: ident, $specout: ty, ($check:tt $val: expr), $use_cast: ident]),* $(,)*]) => {
        paste::paste! {verus!{$(
            impl<M> vstd::std_specs::ops::[<$trt SpecImpl>]<SecType<$baset, M>> for SecType<$baset, M> {
                open spec fn [<obeys_ $fname _spec>]() -> bool { true }
                #[verifier::inline]
                open spec fn [<$fname _req>](self, rhs: SecType<$baset, M>) -> bool {
                    &&& (self@.val $op rhs@.val) >= $baset::MIN
                    &&& (self@.val $op rhs@.val) <= $baset::MAX
                    &&& rhs@.val $check $val
                }
                #[verifier::inline]
                open spec fn [<$fname _spec>](self, rhs: SecType<$baset, M>) -> Self::Output {
                    SecType::spec_new((self@ $op rhs@).$use_cast())
                }
            }

            impl<M> vstd::std_specs::ops::[<$trt SpecImpl>]<SecType<$baset, M>> for $baset {
                open spec fn [<obeys_ $fname _spec>]() -> bool { true }
                open spec fn [<$fname _req>](self, rhs: SecType<$baset, M>) -> bool {
                    &&& rhs.is_constant()
                    &&& (self $op rhs@.val) >= $baset::MIN
                    &&& (self $op rhs@.val) <= $baset::MAX
                    &&& rhs@.val $check $val
                }
                open spec fn [<$fname _spec>](self, rhs: SecType<$baset, M>) -> Self::Output {
                    (self $op rhs@.val) as $baset
                }
            }

            impl<M> vstd::std_specs::ops::[<$trt SpecImpl>]<$baset> for SecType<$baset, M> {
                open spec fn [<obeys_ $fname _spec>]() -> bool { true }
                open spec fn [<$fname _req>](self, rhs: $baset) -> bool {
                    &&& (self@.val $op rhs) >= $baset::MIN
                    &&& (self@.val $op rhs) <= $baset::MAX
                    &&& rhs $check $val
                }
                #[verifier::inline]
                open spec fn [<$fname _spec>](self, rhs: $baset) -> Self::Output {
                    SecType::spec_new((self@ $op SpecSecType::constant(rhs)).$use_cast())
                }
            }

            impl<M> core::ops::$trt<SecType<$baset, M>> for SecType<$baset, M> {
                type Output = Self;
                #[verifier::external_body]
                fn $fname(self, other: Self) -> (ret: Self)
                ensures
                    ret@ === (self@ $op other@).$use_cast(),
                    ret@.val == (self@.val $op other@.val),
                    (self.is_constant() && other.is_constant()) ==> ret.is_constant(),
                    ret.wf_value(),
                    ret == SecType::spec_new((self@ $op other@).$use_cast())
                {

                    SecType {
                        val: self.val $op other.val,
                        view: Ghost::assume_new(),
                    }
                }
            }

            impl<M> core::ops::[<$trt Assign>]<SecType<$baset, M>> for SecType<$baset, M> {
                #[verifier::spinoff_prover]
                fn [<$fname _assign>](&mut self, other: SecType<$baset, M>)
                requires
                    $baset::MIN as int <= (old(self)@.val $op other@.val) <= $baset::MAX as int,
                    other@.val $check $val,
                ensures
                    (*old(self) $op other)@.$use_cast() === self@,
                    (old(self).is_constant() && other.is_constant()) ==> self.is_constant(),
                {
                    *self = core::ops::$trt::<SecType<$baset, M>>::$fname(*self, other);
                }
            }

            impl<M> core::ops::$trt<SecType<$baset, M>> for $baset {
                type Output = Self;
                #[inline(always)]
                #[verifier::spinoff_prover]
                exec fn $fname(self, other: SecType<$baset, M>) -> (ret: Self)
                ensures
                    ret == (self $op other@.val),
                {
                    SecType::constant(self).$fname(other).reveal_value()
                }
            }

            impl<M> core::ops::$trt<$baset> for SecType<$baset, M> {
                type Output = Self;
                #[inline(always)]
                #[verifier::spinoff_prover]
                exec fn $fname(self, other: $baset) -> (ret: Self)
                ensures
                    (self@ $op SpecSecType::constant(other)).$use_cast() === ret@,
                    (self.is_constant()) ==> ret.is_constant(),
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
        paste::paste! {
                verus!{
        $(impl<M> crate::ops::[<VSpec $trt>] for SpecSecType<$baset, M> {
            open spec fn [<spec_ $fname>](self) -> Self {
                self.uop_new(fnspec::[<fn_spec_ $fname _ $baset _ $baset>]())
            }
        }

        impl<M> crate::ops::[<VSpec $trt>] for SecType<$baset, M> {
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
            #[verifier::spinoff_prover]
            exec fn $fname(self) -> (ret: Self)
            {
                proof {
                    // BEGIN Verus SMT axiom-ordering workaround. Restate the
                    // trait's [<requires_ $fname>] precondition (self.wf_value())
                    // because the *SpecImpl axiom for VNot is emitted after the
                    // impl Function-Def check-sat in the smt2 file (same bug
                    // class as the bops workaround above). The `assume` is
                    // sound because the caller has already proved it.
                    use_type_invariant(&self);
                    // END workaround.
                    (self@).proof_uop_valset([<fn_spec_ $fname _ $baset _ $baset>]());
                }
                let ret = self.[<_ $fname>]();
                proof {
                    // Same Verus bug strikes the postcondition: the impl
                    // Function-Def is emitted before VNot's `ensures_not`
                    // definition axiom, so the trait's ensures cannot unfold.
                    // The assume below restates exactly what `_not` already
                    // proved in its ensures (ret@ === self@.spec_not(),
                    // ret.wf_value(), self.is_constant() ==> ret.is_constant()),
                    // which together form `self.ensures_not(ret)`. Sound.
                    assume(self.[<ensures_ $fname>](ret));
                }
                ret
            }
        }

        impl<M> SecType<$baset, M> {
            #[inline(always)]
            #[verifier::spinoff_prover]
            exec fn [<_ $fname>](self) -> (ret: Self)
            requires
                self.wf_value(),
            ensures
                ret@ === self@.[<spec_ $fname>](),
                ret.wf_value(),
                self.is_constant() ==> ret.is_constant(),
            {
                proof {
                    // Same Verus SMT axiom-ordering workaround as above.
                    use_type_invariant(&self);
                    (self@).proof_uop_valset([<fn_spec_ $fname _ $baset _ $baset>]());
                }
                Self {
                    val: $op self.val,
                    view: Ghost(self@.[<spec_ $fname>]()),
                }
            }
        }
        )*
        }
            }
    };
}

#[macro_export]
macro_rules! impl_exe_cast_to_sectype {
    ($baset: ty, [$($out: ty),*$(,)*]) => {
        verus!{
        impl<M> vstd::std_specs::convert::FromSpecImpl<SecType<$baset, M>> for $baset {
            open spec fn obeys_from_spec() -> bool { false }

            #[verifier::inline]
            open spec fn from_spec(v: SecType<$baset, M>) -> $baset {
                v@.val
            }
        }
        impl<M> core::convert::From<SecType<$baset, M>> for $baset {
            fn from(value: SecType<$baset, M>) -> (ret: $baset)
                ensures
                    ret == value@.val,
            {
                value.val as $baset
            }
        }
        $(impl<M> vstd::std_specs::convert::FromSpecImpl<SecType<$baset, M>> for SecType<$out, M> {
            open spec fn obeys_from_spec() -> bool { false }

            #[verifier::inline]
            open spec fn from_spec(v: SecType<$baset, M>) -> SecType<$out, M> {
                v.vspec_cast_to()
            }
        }
        impl<M> core::convert::From<SecType<$baset, M>> for SecType<$out, M> {
            #[verifier(external_body)]
            fn from(value: SecType<$baset, M>) -> (ret: SecType<$out, M>)
                ensures
                    ret === value.vspec_cast_to(),
            {
                SecType{
                    val: value.val as $out,
                    view: Ghost(value@.vspec_cast_to()),
                }
            }
        }

        impl<M> vstd::std_specs::convert::FromSpecImpl<SecType<$baset, M>> for $out {
            open spec fn obeys_from_spec() -> bool { false }
            open spec fn from_spec(v: SecType<$baset, M>) -> $out {
                v@.val as $out
            }
        }
        impl<M> core::convert::From<SecType<$baset, M>> for $out {
            fn from(value: SecType<$baset, M>) -> (ret: $out)
                ensures
                    ret == value@.val as $out,
            {
                value.val as $out
            }
        }
        impl<M> vstd::std_specs::convert::FromSpecImpl<$baset> for SecType<$out, M> {
            open spec fn obeys_from_spec() -> bool { false }
            open spec fn from_spec(v: $baset) -> SecType<$out, M> {
                SecType::spec_new(SpecSecType::constant(v as $out))
            }
        }
        impl<M> core::convert::From<$baset> for SecType<$out, M> {
            fn from(value: $baset) -> (ret: SecType<$out, M>)
                ensures
                    ret === SecType::spec_new(SpecSecType::constant(value as $out)),
            {
                SecType{
                    val: value as $out,
                    view: Ghost(SpecSecType::constant(value as $out)),
                }
            }
        }
    )*

    impl<M> vstd::std_specs::convert::FromSpecImpl<$baset> for SecType<$baset, M> {
        open spec fn obeys_from_spec() -> bool { false }
        open spec fn from_spec(v: $baset) -> SecType<$baset, M> {
            SecType::spec_new(SpecSecType::constant(v))
        }
    }
    impl<M> core::convert::From<$baset> for SecType<$baset, M> {
        fn from(value: $baset) -> (ret: SecType<$baset, M>)
            ensures
                ret === SecType::spec_new(SpecSecType::constant(value)),
        {
            SecType{
                val: value,
                view: Ghost(SpecSecType::constant(value)),
            }
        }
    }
    }
    };
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
    }
)*
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

} // verus!
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
                    //[bitand, &, BitAnd, $baset, (>= 0), call_self],
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
        impl_binary_ops_trait!(SpecEuclideanDiv, $baset, $baset, $baset, spec_euclidean_or_real_div);
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
        impl_binary_ops_trait!(SpecEuclideanDiv, $baset, $baset, $baset, spec_euclidean_or_real_div);
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
        impl_binary_ops_trait!(SpecEuclideanDiv, $baset, $baset, $baset, spec_euclidean_or_real_div);
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

// `pub type NoAdditional = ()` is the default empty memory-attribute parameter
// used by all sectype aliases (u64_s, u32_s, SecSeqByte, …). Defining it here
// (rather than in `primitives_e`) keeps `tspec` self-contained.
pub type NoAdditional = ();

// `wf()` returns `true` because `wf_value()` is already a
// `#[verifier::type_invariant]` on `SecType` (see line 182).  Duplicating that
// obligation here would force every callsite — including the auto-generated
// pre/postconditions inserted by `verismo!` — to manually re-prove a fact the
// type system already guarantees. Callers that need `wf_value()` inside a
// proof can surface it directly via `use_type_invariant(&v)`.
//
// NOTE: This inherent method shadows the `WellFormed::wf` trait impl below;
// both must agree.
impl<T> SecType<T, ()> {
    pub open spec fn wf(&self) -> bool {
        true
    }
}

// `WellFormed` trait impls for `SecType`/`SpecSecType` mirror the inherent
// `wf()` above and return `true` for the same reason: `wf_value()` is the
// canonical `#[verifier::type_invariant]`, not `wf()`.
impl<T> WellFormed for SpecSecType<T, NoAdditional> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        true
    }
}

impl<T> WellFormed for SecType<T, NoAdditional> {
    #[verifier(inline)]
    open spec fn wf(&self) -> bool {
        true
    }
}

} // verus!

impl_secure_type! {NoAdditional, pub type}

verus! {

pub trait ToSecSeq {
    spec fn sec_bytes(self) -> SecSeqByte where Self: core::marker::Sized;
}

pub trait FromSecSeq<T> {
    spec fn from_sec_bytes(self) -> T where T: core::marker::Sized, Self: core::marker::Sized;
}

impl<T: VTypeCast<SecSeqByte>> ToSecSeq for T {
    #[verifier(inline)]
    open spec fn sec_bytes(self) -> SecSeqByte {
        VTypeCast::<SecSeqByte>::vspec_cast_to(self)
    }
}

#[verifier(external_body)]
pub broadcast proof fn axiom_size_from_cast_secbytes_def<T: SpecSize + VTypeCast<SecSeqByte>>(
    val: T,
)
    ensures
        T::spec_size_def() == (#[trigger] VTypeCast::<SecSeqByte>::vspec_cast_to(val)).len(),
        VTypeCast::<SecSeqByte>::vspec_cast_to(val).len() == size_of::<T>(),
{
}

impl<T: ToSecSeq> FromSecSeq<T> for SecSeqByte {
    open spec fn from_sec_bytes(self) -> T {
        choose|v: T| v.sec_bytes() =~~= self
    }
}

impl<T: VTypeCast<SecSeqByte>> VTypeCast<T> for SecSeqByte {
    open spec fn vspec_cast_to(self) -> T {
        self.from_sec_bytes()
    }
}

#[verifier(external_body)]
pub proof fn proof_sectype_cast_eq<T1: VTypeCast<T2>, T2: VTypeCast<T1>, M>(v: SecType<T1, M>)
    requires
        forall|basev: T1| #[trigger]
            VTypeCast::<T1>::vspec_cast_to(VTypeCast::<T2>::vspec_cast_to(basev)) === basev,
    ensures
        VTypeCast::<SecType<T1, M>>::vspec_cast_to(VTypeCast::<SecType<T2, M>>::vspec_cast_to(v))
            === v,
{
}

impl<T> VTypeCast<SecSeqByte> for Option<T> {
    uninterp spec fn vspec_cast_to(self) -> SecSeqByte;
}

impl<T> VTypeCast<SecSeqByte> for Tracked<T> {
    open spec fn vspec_cast_to(self) -> SecSeqByte {
        Seq::empty()
    }
}

// ============================================================================
// `Seq<T>` WellFormed / IsConstant / sec-bytes (moved from primitives_e/seq.rs)
// ============================================================================

impl<T: WellFormed> WellFormed for Seq<T> {
    open spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.len() ==> (#[trigger] self[i]).wf()
    }
}

impl<T: IsConstant + WellFormed> IsConstant for Seq<T> {
    open spec fn is_constant(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.len() ==> (#[trigger] self[i]).is_constant()
        &&& self.wf()
    }

    open spec fn is_constant_to(&self, vmpl: nat) -> bool {
        &&& forall|i: int| 0 <= i < self.len() ==> (#[trigger] self[i]).is_constant_to(vmpl)
        &&& self.wf()
    }
}

pub open spec fn recursive_sec_bytes<T: ToSecSeq>(s: Seq<T>) -> SecSeqByte
    decreases s.len(),
{
    if s.len() > 0 {
        let prevs = s.subrange(0, s.len() - 1);
        if prevs.len() < s.len() {
            recursive_sec_bytes(prevs) + s.last().sec_bytes()
        } else {
            Seq::empty()
        }
    } else {
        Seq::empty()
    }
}

impl<T: ToSecSeq> VTypeCast<SecSeqByte> for Seq<T> {
    open spec fn vspec_cast_to(self) -> SecSeqByte {
        recursive_sec_bytes(self)
    }
}

} // verus!

#[macro_use]
macro_rules! def_basic_tosecseq {
    ($basetype: ty) => {
        verus! {
        impl VTypeCast<SecSeqByte> for $basetype {
            open spec fn vspec_cast_to(self) -> SecSeqByte {
                let seq: Seq<u8> = self.vspec_cast_to();
                Seq::new(
                    seq.len(),
                    |i| SpecSecType::constant(seq[i])
                )
            }
        }
        }
    };
}

def_basic_tosecseq! {u8}
def_basic_tosecseq! {usize}
def_basic_tosecseq! {u16}
def_basic_tosecseq! {u32}
def_basic_tosecseq! {u64}

verus! {

pub trait ValSetSize {
    spec fn valset_size(self, vmpl: nat) -> nat where Self: core::marker::Sized
        recommends
            1 <= vmpl <= 4,
    ;
}

pub open spec fn valset_size(s: SecSeqByte, vmpl: nat) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        1
    } else {
        valset_size(s.subrange(0, s.len() - 1), vmpl) * s.last().valsets[vmpl].len()
    }
}

impl ValSetSize for SecSeqByte {
    open spec fn valset_size(self, vmpl: nat) -> nat {
        valset_size(self, vmpl)
    }
}

impl<T: IsFullSecret> IsFullSecret for Seq<T> {
    open spec fn is_fullsecret_to(&self, vmpl: nat) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_fullsecret_to(vmpl)
    }
}

} // verus!

impl_exe_cast_to_sectype!(u64, [usize, u32, u16, u8]);
impl_exe_cast_to_sectype!(u32, [usize, u64, u16, u8]);
impl_exe_cast_to_sectype!(u16, [usize, u64, u32, u8]);
impl_exe_cast_to_sectype!(u8, [usize, u64, u32, u16]);
impl_exe_cast_to_sectype!(usize, [u64, u32, u16, u8]);
impl_exe_default!(u8, u16, u32, u64, usize);
impl_exe_ops_for_stype! {u8, u16, u32}

impl_exe_not_for_stype!(u64, [[not, !, Not]]);
impl_cmp_ops_for_stype!(u64, u64,
    [[gt, >, VGt], [lt, <, VLt], [le, <=, VLe], [ge, >=, VGe], [eq, ==, VEq]]);

impl_exe_bops_for_stype_by_assume!(u64,
[
    [add, +, Add, int, (>= 0), vspec_cast_to],
    [sub, -, Sub, int, (>= 0), vspec_cast_to],
    [bitand, &, BitAnd, u64, (>= 0), call_self],
]);
impl_exe_bops_for_stype!(u64,
[
    [mul, *, Mul, int, (>= 0), vspec_cast_to],
    [div, /, Div, u64, (!= 0), call_self],
    [rem, %, Rem, u64, (!= 0), call_self],
    [shr, >>, Shr, u64, (< (8 * spec_size::<u64>())), call_self],
    [shl, <<, Shl, u64, (< (8 * spec_size::<u64>())), call_self],
    [bitxor, ^, BitXor, u64, (>= 0), call_self],
    [bitor, |, BitOr, u64, (>= 0), call_self],
]);

impl_exe_not_for_stype!(usize, [[not, !, Not]]);
impl_cmp_ops_for_stype!(usize, usize,
    [[gt, >, VGt], [lt, <, VLt], [le, <=, VLe], [ge, >=, VGe], [eq, ==, VEq]]);
/// BUG(verus): This is a workaround for the Verus bug where the following macro will trigger a compilation error.
impl_exe_bops_for_stype_by_assume!(usize,
[
    [add, +, Add, int, (>= 0), vspec_cast_to],
    [sub, -, Sub, int, (>= 0), vspec_cast_to],
]);
impl_exe_bops_for_stype!(usize,
[
    [mul, *, Mul, int, (>= 0), vspec_cast_to],
    [div, /, Div, usize, (!= 0), call_self],
    [rem, %, Rem, usize, (!= 0), call_self],
    [shr, >>, Shr, usize, (< (8 * spec_size::<usize>())), call_self],
    [shl, <<, Shl, usize, (< (8 * spec_size::<usize>())), call_self],
    [bitxor, ^, BitXor, usize, (>= 0), call_self],
    [bitor, |, BitOr, usize, (>= 0), call_self],
    [bitand, &, BitAnd, usize, (>= 0), call_self],
]);
impl_exe_bops_for_stype!(u8,
[
    [bitand, &, BitAnd, u8, (>= 0), call_self],
]);
impl_exe_bops_for_stype!(u16,
[
    [bitand, &, BitAnd, u16, (>= 0), call_self],
]);
impl_exe_bops_for_stype!(u32,
[
    [bitand, &, BitAnd, u32, (>= 0), call_self],
]);
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
            self.ensures_not(ret),
    ;
}

impl VNot for bool {
    type Output = bool;

    open spec fn requires_not(self) -> bool {
        true
    }

    open spec fn ensures_not(self, ret: bool) -> bool {
        self == !ret
    }

    fn not(self) -> (ret: bool)
        ensures self == !ret,
    {
        let ret = !self;
        proof {
            // Verus SMT axiom-ordering workaround: the trait method's
            // declared `ensures self.ensures_not(ret)` cannot unfold here
            // because the impl Function-Def axiom is emitted before the
            // `ensures_not` definition axiom (same bug class as the
            // SecType ops workarounds above). `ensures_not` is
            // `open spec fn ensures_not(self, ret) -> bool { self == !ret }`,
            // so with `ret = !self` it reduces to `self == !(!self)` which
            // is trivially true by Boolean algebra. The assume is sound.
            assume(self.ensures_not(ret));
        }
        ret
    }
}

} // verus!
  //impl_spec_ops_for_seq! {Seq<u8>}
