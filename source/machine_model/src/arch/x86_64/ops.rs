use super::control::ControlReg;
use super::flags::{
    lemma_same_control_flags_preserves_df, lemma_with_alignment_check_preserves_df, Cr0Value,
    Cr3Value, Cr4Value, RflagsValue,
};

use super::spec::{cpl, Cr0, Cr3, Cr4, Cs, Msr, Rflags};
use crate::register::points_to::{AsmRegisterPointsTo, RustRegisterPointsTo};
use crate::register::reg_trait::ReadableReg;
use core::arch::asm;
use vstd::prelude::*;

/// Implements `ControlReg` for a control-register marker, given its flags type
/// `$value` and the `$stored` normalization of a written value.
///
/// Trusted `asm!` options: reads are `nomem, nostack`; writes are `nostack` only,
/// since a `MOV to CRn` can change how memory is translated or cached. Neither is
/// `preserves_flags`, matching the mutable `Rflags` token in the contract.
macro_rules! control_reg_impl {
    (
        $ty:ident, $value:ident, $read_asm:literal, $write_asm:literal, |$v:ident| $stored:expr
    ) => {
        verus! {

        impl ControlReg for $ty {
            open spec fn stored_value(&self, $v: $value) -> $value {
                $stored
            }

            #[inline(always)]
            #[verifier(external_body)]
            fn asm_read(
                &self,
                Tracked(_cs): Tracked<&AsmRegisterPointsTo<Cs>>,
                Tracked(_rflags): Tracked<&mut AsmRegisterPointsTo<Rflags>>,
                Tracked(token): Tracked<&AsmRegisterPointsTo<Self>>,
            ) -> (result: $value) {
                let output: u64;
                unsafe {
                    asm!(
                        $read_asm,
                        out(reg) output,
                        options(nomem, nostack),
                    );
                }
                $value::from_bits_retain(output)
            }

            #[inline(always)]
            #[verifier(external_body)]
            fn asm_write(
                &self,
                value: $value,
                Tracked(_cs): Tracked<&AsmRegisterPointsTo<Cs>>,
                Tracked(_rflags): Tracked<&mut AsmRegisterPointsTo<Rflags>>,
                Tracked(token): Tracked<&mut AsmRegisterPointsTo<Self>>,
            ) {
                let input: u64 = value.bits();
                unsafe {
                    asm!(
                        $write_asm,
                        in(reg) input,
                        options(nostack),
                    );
                }
            }
        }

        /// Verified layer: the Rust-ABI tokens exec code actually holds.
        impl $ty {
            #[inline(always)]
            pub fn read(
                &self,
                Tracked(cs): Tracked<&RustRegisterPointsTo<Cs>>,
                Tracked(rflags): Tracked<&mut RustRegisterPointsTo<Rflags>>,
                Tracked(token): Tracked<&RustRegisterPointsTo<$ty>>,
            ) -> (result: $value)
                requires
                    cpl(cs.value()) == 0,
                ensures
                    token.value() == result,
                    final(rflags).value().same_control_flags(old(rflags).value()),
            {
                proof {
                    use_type_invariant(&*rflags);
                }
                self.asm_read(Tracked(&cs.asm), Tracked(&mut rflags.asm), Tracked(&token.asm))
            }

            #[inline(always)]
            pub fn write(
                &self,
                value: $value,
                Tracked(cs): Tracked<&RustRegisterPointsTo<Cs>>,
                Tracked(rflags): Tracked<&mut RustRegisterPointsTo<Rflags>>,
                Tracked(token): Tracked<&mut RustRegisterPointsTo<$ty>>,
            )
                requires
                    cpl(cs.value()) == 0,
                ensures
                    final(token).value() == self.stored_value(value),
                    final(rflags).value().same_control_flags(old(rflags).value()),
            {
                proof {
                    use_type_invariant(&*rflags);
                }
                self.asm_write(
                    value,
                    Tracked(&cs.asm),
                    Tracked(&mut rflags.asm),
                    Tracked(&mut token.asm),
                )
            }
        }

        } // verus!
    };
}

// CR0.ET is fixed to 1, so it reads back set regardless of the written value.
control_reg_impl!(Cr0, Cr0Value, "mov {}, cr0", "mov cr0, {}", |value| value.union(Cr0Value::ET));
// CR3 bit 63 is the write-only "no-flush" control and never persists.
control_reg_impl!(Cr3, Cr3Value, "mov {}, cr3", "mov cr3, {}", |value| value
    .difference(Cr3Value::NOFLUSH));
// Every CR4 bit modeled here is retained as written.
control_reg_impl!(Cr4, Cr4Value, "mov {}, cr4", "mov cr4, {}", |value| value);

verus! {

broadcast use {lemma_same_control_flags_preserves_df, lemma_with_alignment_check_preserves_df};

impl ReadableReg for Rflags {
    /// Read the RFLAGS image with `PUSHFQ`/`POP`, storing the popped word
    /// verbatim.
    ///
    /// Trusted: the `external_body` postcondition binds the result to the token's
    /// ghost value. `PUSHFQ`/`POP` only reads the flags, so `preserves_flags` is
    /// accurate; it touches the stack, so neither `nomem` nor `nostack` applies.
    #[inline(always)]
    #[verifier(external_body)]
    fn asm_read(&self, Tracked(token): Tracked<&AsmRegisterPointsTo<Self>>) -> (result:
        RflagsValue) {
        let output: u64;
        unsafe {
            asm!(
                "pushfq",
                "pop {}",
                out(reg) output,
                options(preserves_flags),
            );
        }
        RflagsValue::from_bits_retain(output)
    }
}

impl Msr {
    /// Read this MSR with `RDMSR`.
    ///
    /// Unlike the other register markers, `Msr` is not a unit struct: identity
    /// lives in the runtime `register` number, so the token is matched against it
    /// explicitly to stop a token for one MSR from authorizing access to another.
    ///
    /// Trusted: `RDMSR` returns the value in `edx:eax` and faults with `#GP`
    /// outside CPL 0 or for an unimplemented register, hence the `Cs` evidence.
    /// It reads no memory and leaves the flags alone.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn asm_read(
        &self,
        Tracked(cs): Tracked<&AsmRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&AsmRegisterPointsTo<Msr>>,
    ) -> (result: u64)
        requires
            cpl(cs.value()) == 0,
            token.reg().register == self.register,
        ensures
            token.value() == result,
        no_unwind
    {
        let (low, high): (u32, u32);
        let register = self.register;
        unsafe {
            asm!(
                "rdmsr",
                in("ecx") register,
                out("eax") low,
                out("edx") high,
                options(nomem, nostack, preserves_flags),
            );
        }
        ((high as u64) << 32u64) | (low as u64)
    }

    /// Write `value` to this MSR with `WRMSR`.
    ///
    /// Models only a *successful* write: `WRMSR` faults with `#GP` outside CPL 0,
    /// for an unimplemented register, or when `value` sets a reserved bit, and
    /// the per-register reserved-bit preconditions are not yet modeled.
    ///
    /// Writing `MSR_EFER` can invalidate a downstream paging invariant, which
    /// callers must then re-establish.
    ///
    /// Trusted: `WRMSR` takes the value in `edx:eax` and leaves the flags alone.
    /// It is not `nomem`, since writing an MSR such as EFER or PAT changes how
    /// memory is translated or cached.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn asm_write(
        &self,
        value: u64,
        Tracked(cs): Tracked<&AsmRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&mut AsmRegisterPointsTo<Msr>>,
    )
        requires
            cpl(cs.value()) == 0,
            old(token).reg().register == self.register,
        ensures
            final(token).value() == value,
            final(token).reg() == old(token).reg(),
        no_unwind
    {
        let low: u32 = value as u32;
        let high: u32 = (value >> 32u64) as u32;
        let register = self.register;
        unsafe {
            asm!(
                "wrmsr",
                in("ecx") register,
                in("eax") low,
                in("edx") high,
                options(nostack, preserves_flags),
            );
        }
    }
}

/// Verified layer: the Rust-ABI tokens exec code actually holds.
impl Msr {
    pub fn read(
        &self,
        Tracked(cs): Tracked<&RustRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&RustRegisterPointsTo<Msr>>,
    ) -> (result: u64)
        requires
            cpl(cs.value()) == 0,
            token.reg().register == self.register,
        ensures
            token.value() == result,
    {
        self.asm_read(Tracked(&cs.asm), Tracked(&token.asm))
    }

    pub fn write(
        &self,
        value: u64,
        Tracked(cs): Tracked<&RustRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&mut RustRegisterPointsTo<Msr>>,
    )
        requires
            cpl(cs.value()) == 0,
            old(token).reg().register == self.register,
        ensures
            final(token).value() == value,
            final(token).reg() == old(token).reg(),
    {
        self.asm_write(value, Tracked(&cs.asm), Tracked(&mut token.asm))
    }
}

impl Rflags {
    /// `STAC`: set RFLAGS.AC, allowing supervisor accesses to user pages under
    /// SMAP.
    ///
    /// Trusted: `STAC` modifies only AC, which is why `preserves_flags` (covering
    /// the status flags and DF) is sound and why the ensured image differs only in
    /// that bit. It faults with `#UD` unless `CR4.SMAP` is set at CPL 0, hence the
    /// `Cr4`/`Cs` evidence.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn asm_stac(
        &self,
        Tracked(cr4): Tracked<&AsmRegisterPointsTo<Cr4>>,
        Tracked(cs): Tracked<&AsmRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&mut AsmRegisterPointsTo<Rflags>>,
    )
        requires
            cr4.value().contains(Cr4Value::SMAP),
            cpl(cs.value()) == 0,
        ensures
            final(token).value() == old(token).value().with_alignment_check(true),
        no_unwind
    {
        unsafe {
            asm!("stac", options(nomem, nostack, preserves_flags));
        }
    }

    /// `CLAC`: clear RFLAGS.AC, restoring SMAP enforcement.
    ///
    /// Trusted for the same reasons as `stac`, whose `#UD` conditions it shares.
    #[inline(always)]
    #[verifier(external_body)]
    pub fn asm_clac(
        &self,
        Tracked(cr4): Tracked<&AsmRegisterPointsTo<Cr4>>,
        Tracked(cs): Tracked<&AsmRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&mut AsmRegisterPointsTo<Rflags>>,
    )
        requires
            cr4.value().contains(Cr4Value::SMAP),
            cpl(cs.value()) == 0,
        ensures
            final(token).value() == old(token).value().with_alignment_check(false),
        no_unwind
    {
        unsafe {
            asm!("clac", options(nomem, nostack, preserves_flags));
        }
    }
}

/// Verified layer: the Rust-ABI tokens exec code actually holds.
impl Rflags {
    pub fn stac(
        &self,
        Tracked(cr4): Tracked<&RustRegisterPointsTo<Cr4>>,
        Tracked(cs): Tracked<&RustRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&mut RustRegisterPointsTo<Rflags>>,
    )
        requires
            cr4.value().contains(Cr4Value::SMAP),
            cpl(cs.value()) == 0,
        ensures
            final(token).value() == old(token).value().with_alignment_check(true),
    {
        proof {
            use_type_invariant(&*token);
        }
        self.asm_stac(Tracked(&cr4.asm), Tracked(&cs.asm), Tracked(&mut token.asm));
    }

    pub fn clac(
        &self,
        Tracked(cr4): Tracked<&RustRegisterPointsTo<Cr4>>,
        Tracked(cs): Tracked<&RustRegisterPointsTo<Cs>>,
        Tracked(token): Tracked<&mut RustRegisterPointsTo<Rflags>>,
    )
        requires
            cr4.value().contains(Cr4Value::SMAP),
            cpl(cs.value()) == 0,
        ensures
            final(token).value() == old(token).value().with_alignment_check(false),
    {
        proof {
            use_type_invariant(&*token);
        }
        self.asm_clac(Tracked(&cr4.asm), Tracked(&cs.asm), Tracked(&mut token.asm));
    }
}

} // verus!
