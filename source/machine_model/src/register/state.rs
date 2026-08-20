use vstd::prelude::*;

verus! {

use super::points_to::*;
use super::spec::*;

/// The complete tracked machine register state: one typed ownership token per
/// modeled register, plus a map of tokens for the model-specific registers,
/// keyed by MSR number.
pub tracked struct RegisterState {
    pub tracked rflags_control: RegisterPointsTo<RflagsControl>,
    pub tracked rax: RegisterPointsTo<Rax>,
    pub tracked rsp: RegisterPointsTo<Rsp>,
    pub tracked cs: RegisterPointsTo<Cs>,
    pub tracked ds: RegisterPointsTo<Ds>,
    pub tracked ss: RegisterPointsTo<Ss>,
    pub tracked es: RegisterPointsTo<Es>,
    pub tracked gs: RegisterPointsTo<Gs>,
    pub tracked cpl: RegisterPointsTo<Cpl>,
    pub tracked cr0: RegisterPointsTo<Cr0>,
    pub tracked cr1: RegisterPointsTo<Cr1>,
    pub tracked cr2: RegisterPointsTo<Cr2>,
    pub tracked cr3: RegisterPointsTo<Cr3>,
    pub tracked cr4: RegisterPointsTo<Cr4>,
    pub tracked xcr0: RegisterPointsTo<Xcr0>,
    pub tracked pkru: RegisterPointsTo<Pkru>,
    pub tracked idtr: RegisterPointsTo<IdtrBaseLimit>,
    pub tracked gdtr: RegisterPointsTo<GdtrBaseLimit>,
    pub tracked msrs: Map<u32, RegisterPointsTo<Msr>>,
}

impl RegisterState {
    /// Every MSR token stored under key `register` really owns MSR `register`.
    /// The fixed-width registers need no such condition: their identity is the
    /// marker type of their token.
    pub open spec fn inv(&self) -> bool {
        forall|register: u32|
            #![trigger self.msrs.dom().contains(register)]
            self.msrs.dom().contains(register) ==> self.msrs[register].reg().register == register
    }
}

} // verus!
