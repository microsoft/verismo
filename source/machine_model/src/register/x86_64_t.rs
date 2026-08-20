use super::points_to::*;
use super::reg_trait::*;
use super::spec::*;
use core::arch::asm;
use vstd::prelude::*;

macro_rules! control_reg_impl {
    ($ty:ident, $read_asm:literal, $write_asm:literal) => {
        verus! {

        impl ReadableReg for $ty {
            #[inline(always)]
            #[verifier(external_body)]
            fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result: u64) {
                let output: u64;
                unsafe {
                    asm!(
                        $read_asm,
                        out(reg) output,
                        options(nomem, nostack),
                    );
                }
                output
            }
        }

        /// Note: writing a control register can invalidate
        /// `PageTableGlobalState::inv` (which constrains CR0/CR3/CR4 and the ghost
        /// mappings). The invariant is relative to the register state, so callers
        /// holding such a state must re-establish it after any control-register
        /// write before relying on it again.
        impl WritableReg for $ty {
            #[inline(always)]
            #[verifier(external_body)]
            fn write(&self, value: u64, Tracked(token): Tracked<&mut RegisterPointsTo<Self>>) {
                let input: u64 = value;
                unsafe {
                    asm!(
                        $write_asm,
                        in(reg) input,
                        options(nostack),
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

impl ReadableReg for RflagsControl {
    /// Read the persistent control/system flags out of RFLAGS.
    ///
    /// `pushfq`/`pop` only reads the flags, so `preserves_flags` is accurate here.
    /// Being `external_body`, the (trusted) postcondition binds the decoded value to
    /// the token's ghost value.
    #[inline(always)]
    #[verifier(external_body)]
    fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result:
        RflagsControlValue) {
        let raw: u64;
        unsafe {
            asm!(
                "pushfq",
                "pop {}",
                out(reg) raw,
                options(preserves_flags),
            );
        }
        RflagsControlValue {
            trap: (raw & RFLAGS_TF) != 0,
            interrupt_enable: (raw & RFLAGS_IF) != 0,
            direction: (raw & RFLAGS_DF) != 0,
            io_privilege_level: ((raw & RFLAGS_IOPL) >> RFLAGS_IOPL_SHIFT) as u8,
            nested_task: (raw & RFLAGS_NT) != 0,
            alignment_check: (raw & RFLAGS_AC) != 0,
            virtual_interrupt: (raw & RFLAGS_VIF) != 0,
            virtual_interrupt_pending: (raw & RFLAGS_VIP) != 0,
            id: (raw & RFLAGS_ID) != 0,
        }
    }
}

impl RflagsControl {
    /// `STAC`: set RFLAGS.AC, allowing supervisor accesses to user pages under SMAP.
    ///
    /// `STAC` only modifies AC, and Rust's `preserves_flags` covers just the
    /// status flags (CF, PF, AF, ZF, SF, OF) plus DF, none of which `STAC` touches,
    /// so the option is sound here.
    ///
    /// `STAC` faults with #UD unless `CR4.SMAP` is set and the current privilege
    /// level is 0, so shared tokens for `Cr4` and `Cpl` are taken as evidence of
    /// both conditions.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn stac(
        &self,
        Tracked(cr4): Tracked<&RegisterPointsTo<Cr4>>,
        Tracked(cpl): Tracked<&RegisterPointsTo<Cpl>>,
        Tracked(token): Tracked<&mut RegisterPointsTo<RflagsControl>>,
    )
        requires
            (cr4.value() & CR4_SMAP) != 0,
            cpl.value() == 0,
        ensures
            final(token).reg() == old(token).reg(),
            final(token).value() == old(token).value().with_alignment_check(true),
    {
        unsafe {
            asm!("stac", options(nomem, nostack, preserves_flags));
        }
    }

    /// `CLAC`: clear RFLAGS.AC, restoring SMAP enforcement.
    ///
    /// See `stac` for why `preserves_flags` is sound and why the `Cr4`/`Cpl` tokens
    /// are required: `CLAC` has the same #UD conditions.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn clac(
        &self,
        Tracked(cr4): Tracked<&RegisterPointsTo<Cr4>>,
        Tracked(cpl): Tracked<&RegisterPointsTo<Cpl>>,
        Tracked(token): Tracked<&mut RegisterPointsTo<RflagsControl>>,
    )
        requires
            (cr4.value() & CR4_SMAP) != 0,
            cpl.value() == 0,
        ensures
            final(token).reg() == old(token).reg(),
            final(token).value() == old(token).value().with_alignment_check(false),
    {
        unsafe {
            asm!("clac", options(nomem, nostack, preserves_flags));
        }
    }
}

} // verus!
