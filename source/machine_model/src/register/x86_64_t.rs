use super::points_to::*;
use super::reg_trait::*;
use super::spec::*;
use core::arch::asm;
use vstd::prelude::*;

/// Implements `ControlReg` for a control-register marker.
///
/// `$stored` is the closed-form normalization applied to a written value: the
/// value that is architecturally retained (and thus read back) after a successful
/// `MOV to CRn`.
///
/// Reads are `nomem, nostack`; writes are `nostack` only, since a `MOV to CRn` can
/// change how memory is translated/cached. Neither is `preserves_flags`: `MOV
/// to/from CRn` leaves the status flags architecturally undefined, which is why both
/// operations take the `Rflags` token mutably and the body need not compute any
/// flag value.
///
/// Writing an invalid/reserved/unsupported value faults (`#GP`); the contract below
/// models only the value retained after a successful write, and full CPU
/// capability/fixed-bit preconditions remain future work. Such a write can also
/// invalidate `PageTableGlobalState::inv`, which callers must re-establish.
macro_rules! control_reg_impl {
    ($ty:ident, $read_asm:literal, $write_asm:literal, |$v:ident| $stored:expr) => {
        verus! {

        impl ControlReg for $ty {
            open spec fn stored_value(&self, $v: u64) -> u64 {
                $stored
            }

            #[inline(always)]
            #[verifier(external_body)]
            fn read(
                &self,
                Tracked(_cpl): Tracked<&RegisterPointsTo<Cpl>>,
                Tracked(_rflags): Tracked<&mut RegisterPointsTo<Rflags>>,
                Tracked(token): Tracked<&RegisterPointsTo<Self>>,
            ) -> (result: u64) {
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

            #[inline(always)]
            #[verifier(external_body)]
            fn write(
                &self,
                value: u64,
                Tracked(_cpl): Tracked<&RegisterPointsTo<Cpl>>,
                Tracked(_rflags): Tracked<&mut RegisterPointsTo<Rflags>>,
                Tracked(token): Tracked<&mut RegisterPointsTo<Self>>,
            ) {
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

// CR0.ET is fixed to 1, so it reads back set regardless of the written value.
control_reg_impl!(Cr0, "mov {}, cr0", "mov cr0, {}", |value| value | CR0_ET);
// CR3 bit 63 is the write-only "no-flush" control and never persists.
control_reg_impl!(Cr3, "mov {}, cr3", "mov cr3, {}", |value| value & !CR3_NOFLUSH);
// Every CR4 bit modeled here is retained as written.
control_reg_impl!(Cr4, "mov {}, cr4", "mov cr4, {}", |value| value);

verus! {

impl ReadableReg for Rflags {
    /// Read the raw RFLAGS image with `PUSHFQ`/`POP`.
    ///
    /// The popped 64-bit word is stored verbatim: no bit is decoded, masked, or
    /// otherwise interpreted here, so the value is exactly the architectural image
    /// `PUSHFQ` produced (with `RF` and `VM` stored as 0 by that instruction).
    ///
    /// `PUSHFQ`/`POP` only reads the flags, so `preserves_flags` is accurate; the
    /// sequence pushes and pops the stack and so is neither `nomem` nor `nostack`.
    /// Being `external_body`, the (trusted) postcondition binds the value to the
    /// token's ghost value.
    #[inline(always)]
    #[verifier(external_body)]
    fn read(&self, Tracked(token): Tracked<&RegisterPointsTo<Self>>) -> (result: RflagsValue) {
        let output: u64;
        unsafe {
            asm!(
                "pushfq",
                "pop {}",
                out(reg) output,
                options(preserves_flags),
            );
        }
        RflagsValue { bits: output }
    }
}

impl Rflags {
    /// `STAC`: set RFLAGS.AC, allowing supervisor accesses to user pages under SMAP.
    ///
    /// `STAC` only modifies AC, and Rust's `preserves_flags` covers just the
    /// status flags (CF, PF, AF, ZF, SF, OF) plus DF, none of which `STAC` touches,
    /// so the option is sound here; correspondingly the resulting raw image differs
    /// from the previous one only in the `AC` bit.
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
        Tracked(token): Tracked<&mut RegisterPointsTo<Rflags>>,
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
        Tracked(token): Tracked<&mut RegisterPointsTo<Rflags>>,
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
