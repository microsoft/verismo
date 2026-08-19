use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum RegisterKind {
    U16,
    U64,
    DescriptorTable,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum RegName {
    Rflags,
    Rax,
    Rsp,
    Cs,
    Ds,
    Ss,
    Es,
    Gs,
    Cpl,
    Cr0,
    Cr1,
    Cr2,
    Cr3,
    Cr4,
    XCr0,
    Pkru,
    IdtrBaseLimit,
    GdtrBaseLimit,
    MSR(u32),
}

impl RegName {
    pub open spec fn kind(self) -> RegisterKind {
        match self {
            RegName::Cs
            | RegName::Ds
            | RegName::Ss
            | RegName::Es
            | RegName::Gs => RegisterKind::U16,
            RegName::IdtrBaseLimit | RegName::GdtrBaseLimit => RegisterKind::DescriptorTable,
            _ => RegisterKind::U64,
        }
    }
}

#[cfg(feature = "verification-test")]
mod verification_test {
    use super::*;

    proof fn check_register_kinds() {
        assert(RegName::Rflags.kind() == RegisterKind::U64);
        assert(RegName::Rax.kind() == RegisterKind::U64);
        assert(RegName::Rsp.kind() == RegisterKind::U64);
        assert(RegName::Cs.kind() == RegisterKind::U16);
        assert(RegName::Ds.kind() == RegisterKind::U16);
        assert(RegName::Ss.kind() == RegisterKind::U16);
        assert(RegName::Es.kind() == RegisterKind::U16);
        assert(RegName::Gs.kind() == RegisterKind::U16);
        assert(RegName::Cpl.kind() == RegisterKind::U64);
        assert(RegName::Cr0.kind() == RegisterKind::U64);
        assert(RegName::Cr1.kind() == RegisterKind::U64);
        assert(RegName::Cr2.kind() == RegisterKind::U64);
        assert(RegName::Cr3.kind() == RegisterKind::U64);
        assert(RegName::Cr4.kind() == RegisterKind::U64);
        assert(RegName::XCr0.kind() == RegisterKind::U64);
        assert(RegName::Pkru.kind() == RegisterKind::U64);
        assert(RegName::IdtrBaseLimit.kind() == RegisterKind::DescriptorTable);
        assert(RegName::GdtrBaseLimit.kind() == RegisterKind::DescriptorTable);
        assert(RegName::MSR(0).kind() == RegisterKind::U64);
    }

}

} // verus!
