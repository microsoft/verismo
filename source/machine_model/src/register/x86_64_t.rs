use super::points_to::*;
use super::reg_trait::*;
use super::spec::*;
use core::arch::asm;
use vstd::prelude::*;

macro_rules! control_reg_impl {
    ($ty:ident, $read_asm:literal, $write_asm:literal) => {
        verus! {

        impl ExecutableReg for $ty {
            #[inline(always)]
            #[verifier(external_body)]
            fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result: u64) {
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
            fn write(&self, value: u64, Tracked(token): Tracked<&mut RegisterPointsTo<Self>>) {
                let input: u64 = value;
                unsafe {
                    asm!(
                        $write_asm,
                        in(reg) input,
                        options(nostack, preserves_flags),
                    );
                }
            }
        }

        } // verus!
    };
}

control_reg_impl!(Cr0, "mov {}, cr0", "mov cr0, {}");
control_reg_impl!(Cr3, "mov {}, cr3", "mov cr3, {}");
control_reg_impl!(Cr4, "mov {}, cr4", "mov cr4, {}");

verus! {

impl ExecutableReg for Rflags {
    #[inline(always)]
    #[verifier(external_body)]
    fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result: u64) {
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
    fn write(&self, value: u64, Tracked(token): Tracked<&mut RegisterPointsTo<Self>>) {
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
