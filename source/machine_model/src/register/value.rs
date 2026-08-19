use vstd::prelude::*;

verus! {
    use super::name::*;

    #[derive(PartialEq, Eq, Copy, Clone, Debug)]
    pub ghost struct DescriptorTableValue {
        pub limit: u16,
        pub base: u64,
    }

    #[derive(PartialEq, Eq, Copy, Clone, Debug)]
    pub ghost enum RegisterValue {
        U16(u16),
        U64(u64),
        DescriptorTable(DescriptorTableValue),
    }

    impl RegisterValue {
        pub open spec fn kind(self) -> RegisterKind {
            match self {
                RegisterValue::U16(_) => RegisterKind::U16,
                RegisterValue::U64(_) => RegisterKind::U64,
                RegisterValue::DescriptorTable(_) => RegisterKind::DescriptorTable,
            }
        }

        pub open spec fn matches(self, register_id: RegName) -> bool {
            self.kind() == register_id.kind()
        }
    }

    #[cfg(feature = "verification-test")]
    mod verification_test {
        use super::*;

        proof fn check_register_values() {
            assert(RegisterValue::U16(0).kind() == RegisterKind::U16);
            assert(RegisterValue::U64(0).kind() == RegisterKind::U64);
            assert(RegisterValue::DescriptorTable(DescriptorTableValue { limit: 0, base: 0 }).kind()
                == RegisterKind::DescriptorTable);

            assert(RegisterValue::U16(0).matches(RegName::Cs));
            assert(!RegisterValue::U16(0).matches(RegName::Cr3));

            assert(RegisterValue::U64(0).matches(RegName::Cr3));
            assert(!RegisterValue::U64(0).matches(RegName::GdtrBaseLimit));

            assert(RegisterValue::DescriptorTable(DescriptorTableValue { limit: 0, base: 0 })
                .matches(RegName::GdtrBaseLimit));
            assert(!RegisterValue::DescriptorTable(DescriptorTableValue { limit: 0, base: 0 })
                .matches(RegName::MSR(0)));
        }
    }
}
