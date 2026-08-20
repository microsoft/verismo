use vstd::prelude::*;

verus! {

use super::name::*;
use super::spec::DescriptorTableValue;

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub ghost enum RegisterValue {
    Rflags(u64),
    Rax(u64),
    Rsp(u64),
    Cs(u16),
    Ds(u16),
    Ss(u16),
    Es(u16),
    Gs(u16),
    Cpl(u64),
    Cr0(u64),
    Cr1(u64),
    Cr2(u64),
    Cr3(u64),
    Cr4(u64),
    XCr0(u64),
    Pkru(u64),
    IdtrBaseLimit(DescriptorTableValue),
    GdtrBaseLimit(DescriptorTableValue),
    MSR { register: u32, value: u64 },
}

impl RegisterValue {
    /// The structurally-determined register identity for this value: every
    /// `RegisterValue` variant corresponds to exactly one `RegName`, so
    /// identity/value mismatches are unrepresentable.
    pub open spec fn register_id(self) -> RegName {
        match self {
            RegisterValue::Rflags(_) => RegName::Rflags,
            RegisterValue::Rax(_) => RegName::Rax,
            RegisterValue::Rsp(_) => RegName::Rsp,
            RegisterValue::Cs(_) => RegName::Cs,
            RegisterValue::Ds(_) => RegName::Ds,
            RegisterValue::Ss(_) => RegName::Ss,
            RegisterValue::Es(_) => RegName::Es,
            RegisterValue::Gs(_) => RegName::Gs,
            RegisterValue::Cpl(_) => RegName::Cpl,
            RegisterValue::Cr0(_) => RegName::Cr0,
            RegisterValue::Cr1(_) => RegName::Cr1,
            RegisterValue::Cr2(_) => RegName::Cr2,
            RegisterValue::Cr3(_) => RegName::Cr3,
            RegisterValue::Cr4(_) => RegName::Cr4,
            RegisterValue::XCr0(_) => RegName::XCr0,
            RegisterValue::Pkru(_) => RegName::Pkru,
            RegisterValue::IdtrBaseLimit(_) => RegName::IdtrBaseLimit,
            RegisterValue::GdtrBaseLimit(_) => RegName::GdtrBaseLimit,
            RegisterValue::MSR { register, value: _ } => RegName::MSR(register),
        }
    }

    pub open spec fn kind(self) -> RegisterKind {
        self.register_id().kind()
    }

    /// Exact identity equality: a value only matches the register it was
    /// structurally constructed for.
    pub open spec fn matches(self, register_id: RegName) -> bool {
        self.register_id() == register_id
    }
}

#[cfg(feature = "verification-test")]
mod verification_test {
    use super::*;

    proof fn check_register_id_fixed_variants() {
        assert(RegisterValue::Rflags(0).register_id() == RegName::Rflags);
        assert(RegisterValue::Rax(0).register_id() == RegName::Rax);
        assert(RegisterValue::Rsp(0).register_id() == RegName::Rsp);
        assert(RegisterValue::Cs(0).register_id() == RegName::Cs);
        assert(RegisterValue::Ds(0).register_id() == RegName::Ds);
        assert(RegisterValue::Ss(0).register_id() == RegName::Ss);
        assert(RegisterValue::Es(0).register_id() == RegName::Es);
        assert(RegisterValue::Gs(0).register_id() == RegName::Gs);
        assert(RegisterValue::Cpl(0).register_id() == RegName::Cpl);
        assert(RegisterValue::Cr0(0).register_id() == RegName::Cr0);
        assert(RegisterValue::Cr1(0).register_id() == RegName::Cr1);
        assert(RegisterValue::Cr2(0).register_id() == RegName::Cr2);
        assert(RegisterValue::Cr3(0).register_id() == RegName::Cr3);
        assert(RegisterValue::Cr4(0).register_id() == RegName::Cr4);
        assert(RegisterValue::XCr0(0).register_id() == RegName::XCr0);
        assert(RegisterValue::Pkru(0).register_id() == RegName::Pkru);
        assert(RegisterValue::IdtrBaseLimit(
            DescriptorTableValue { limit: 0, base: 0 },
        ).register_id() == RegName::IdtrBaseLimit);
        assert(RegisterValue::GdtrBaseLimit(
            DescriptorTableValue { limit: 0, base: 0 },
        ).register_id() == RegName::GdtrBaseLimit);
    }

    proof fn check_register_id_msr() {
        assert(RegisterValue::MSR { register: 0xC000_0080, value: 0 }.register_id() == RegName::MSR(
            0xC000_0080,
        ));
        assert(RegisterValue::MSR { register: 1, value: 0 }.register_id() == RegName::MSR(1));
        assert(!(RegisterValue::MSR { register: 1, value: 0 }.register_id() == RegName::MSR(2)));
    }

    proof fn check_register_kinds() {
        assert(RegisterValue::Cs(0).kind() == RegisterKind::U16);
        assert(RegisterValue::Rax(0).kind() == RegisterKind::U64);
        assert(RegisterValue::IdtrBaseLimit(DescriptorTableValue { limit: 0, base: 0 }).kind()
            == RegisterKind::DescriptorTable);
    }

    proof fn check_register_matches_exact_identity() {
        assert(RegisterValue::Cr3(0).matches(RegName::Cr3));
        assert(!RegisterValue::Cr3(0).matches(RegName::Cr4));
        assert(!RegisterValue::Cr4(0).matches(RegName::Cr3));

        assert(RegisterValue::Cs(0).matches(RegName::Cs));
        assert(!RegisterValue::Cs(0).matches(RegName::Ds));

        assert(RegisterValue::Pkru(0).matches(RegName::Pkru));
        assert(!RegisterValue::Pkru(0).matches(RegName::XCr0));

        assert(RegisterValue::GdtrBaseLimit(DescriptorTableValue { limit: 0, base: 0 }).matches(
            RegName::GdtrBaseLimit,
        ));
        assert(!RegisterValue::GdtrBaseLimit(DescriptorTableValue { limit: 0, base: 0 }).matches(
            RegName::IdtrBaseLimit,
        ));

        assert(RegisterValue::MSR { register: 5, value: 0 }.matches(RegName::MSR(5)));
        assert(!RegisterValue::MSR { register: 5, value: 0 }.matches(RegName::MSR(6)));
    }

}

} // verus!
