use vstd::prelude::*;

verus! {

use super::spec::{
    Cr0,
    Cr1,
    Cr2,
    Cr3,
    Cr4,
    Cs,
    Ds,
    Es,
    GdtrBaseLimit,
    Gs,
    IdtrBaseLimit,
    Msr,
    Pkru,
    Rax,
    Rflags,
    Rsp,
    Ss,
    Xcr0,
};
use crate::register::points_to::RustRegisterPointsTo;

/// The complete tracked machine register state: one typed ownership token per
/// modeled register, plus a map of tokens for the model-specific registers,
/// keyed by MSR number.
pub tracked struct RegisterState {
    pub tracked rflags: RustRegisterPointsTo<Rflags>,
    pub tracked rax: RustRegisterPointsTo<Rax>,
    pub tracked rsp: RustRegisterPointsTo<Rsp>,
    pub tracked cs: RustRegisterPointsTo<Cs>,
    pub tracked ds: RustRegisterPointsTo<Ds>,
    pub tracked ss: RustRegisterPointsTo<Ss>,
    pub tracked es: RustRegisterPointsTo<Es>,
    pub tracked gs: RustRegisterPointsTo<Gs>,
    pub tracked cr0: RustRegisterPointsTo<Cr0>,
    pub tracked cr1: RustRegisterPointsTo<Cr1>,
    pub tracked cr2: RustRegisterPointsTo<Cr2>,
    pub tracked cr3: RustRegisterPointsTo<Cr3>,
    pub tracked cr4: RustRegisterPointsTo<Cr4>,
    pub tracked xcr0: RustRegisterPointsTo<Xcr0>,
    pub tracked pkru: RustRegisterPointsTo<Pkru>,
    pub tracked idtr: RustRegisterPointsTo<IdtrBaseLimit>,
    pub tracked gdtr: RustRegisterPointsTo<GdtrBaseLimit>,
    pub tracked msrs: MsrMap,
}

/// The tokens for the model-specific registers, keyed by MSR number.
///
/// The map is private so that the key-agreement invariant below can be a type
/// invariant: a token stored under key `register` always owns MSR `register`.
pub tracked struct MsrMap {
    tracked map: Map<u32, RustRegisterPointsTo<Msr>>,
}

impl MsrMap {
    /// Every MSR token stored under key `register` really owns MSR `register`.
    /// The fixed-width registers need no such condition: their identity is the
    /// marker type of their token.
    #[verifier::type_invariant]
    spec fn inv(&self) -> bool {
        forall|register: u32|
            #![trigger self.map.dom().contains(register)]
            self.map.dom().contains(register) ==> self.map[register].reg().register == register
    }

    pub closed spec fn dom(&self) -> Set<u32> {
        self.map.dom()
    }

    pub closed spec fn index(&self, register: u32) -> RustRegisterPointsTo<Msr> {
        self.map[register]
    }

    pub proof fn borrow(tracked &self, register: u32) -> (tracked token: &RustRegisterPointsTo<Msr>)
        requires
            self.dom().contains(register),
        ensures
            *token == self.index(register),
            token.reg().register == register,
    {
        use_type_invariant(self);
        self.map.tracked_borrow(register)
    }

    pub proof fn remove(tracked &mut self, register: u32) -> (tracked token: RustRegisterPointsTo<
        Msr,
    >)
        requires
            old(self).dom().contains(register),
        ensures
            token == old(self).index(register),
            token.reg().register == register,
            final(self).dom() == old(self).dom().remove(register),
            forall|other: u32|
                #![trigger final(self).index(other)]
                other != register ==> final(self).index(other) == old(self).index(other),
    {
        use_type_invariant(&*self);
        self.map.tracked_remove(register)
    }

    pub proof fn insert(tracked &mut self, register: u32, tracked token: RustRegisterPointsTo<Msr>)
        requires
            token.reg().register == register,
        ensures
            final(self).dom() == old(self).dom().insert(register),
            final(self).index(register) == token,
            forall|other: u32|
                #![trigger final(self).index(other)]
                other != register ==> final(self).index(other) == old(self).index(other),
    {
        use_type_invariant(&*self);
        self.map.tracked_insert(register, token)
    }
}

} // verus!
