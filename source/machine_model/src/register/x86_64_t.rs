use super::name::*;
use super::points_to::*;
use super::r#trait::*;
use super::value::*;
use core::arch::asm;
use vstd::prelude::*;

macro_rules! control_reg_impl {
    ($ty:ident, $reg_name:ident, $variant:ident, $read_asm:literal, $write_asm:literal) => {
        verus! {

        #[derive(Copy, Clone, Debug)]
        pub struct $ty;

        impl AnyRegTrait<u64> for $ty {
            open spec fn reg_id(&self) -> RegName {
                RegName::$reg_name
            }

            open spec fn reg_value(&self, value: u64) -> RegisterValue {
                RegisterValue::$variant(value)
            }

            proof fn reg_value_id(&self, value: u64) {
            }

            #[inline(always)]
            #[verifier(external_body)]
            fn read(&self, Tracked(token): Tracked<&RegisterPointsTo>) -> (result: u64) {
                let output: u64;
                unsafe {
                    asm!(
                        $read_asm,
                        out(reg) output,
                        options(nomem, nostack, preserves_flags),
                    );
                }
                output
            }

            #[inline(always)]
            #[verifier(external_body)]
            fn write(&self, value: u64, Tracked(token): Tracked<&mut RegisterPointsTo>) {
                let input: u64 = value;
                unsafe {
                    asm!(
                        $write_asm,
                        in(reg) input,
                        options(nomem, nostack, preserves_flags),
                    );
                }
            }
        }

        } // verus!
    };
}

control_reg_impl!(CR0, Cr0, Cr0, "mov {}, cr0", "mov cr0, {}");
control_reg_impl!(CR3, Cr3, Cr3, "mov {}, cr3", "mov cr3, {}");
control_reg_impl!(CR4, Cr4, Cr4, "mov {}, cr4", "mov cr4, {}");

verus! {

#[derive(Copy, Clone, Debug)]
pub struct RFLAGS;

impl AnyRegTrait<u64> for RFLAGS {
    open spec fn reg_id(&self) -> RegName {
        RegName::Rflags
    }

    open spec fn reg_value(&self, value: u64) -> RegisterValue {
        RegisterValue::Rflags(value)
    }

    proof fn reg_value_id(&self, value: u64) {
    }

    #[inline(always)]
    #[verifier(external_body)]
    fn read(&self, Tracked(token): Tracked<&RegisterPointsTo>) -> (result: u64) {
        let output: u64;
        unsafe {
            asm!(
                "pushfq",
                "pop {}",
                out(reg) output,
                options(preserves_flags),
            );
        }
        output
    }

    #[inline(always)]
    #[verifier(external_body)]
    fn write(&self, value: u64, Tracked(token): Tracked<&mut RegisterPointsTo>) {
        let input: u64 = value;
        unsafe {
            asm!(
                "push {}",
                "popfq",
                in(reg) input,
            );
        }
    }
}

} // verus!
