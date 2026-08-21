// Every register, instruction and ABI rule modeled below is architecture
// specific, including `RegSpec::rust_abi_wf`, which encodes the inline-asm
// guarantee that RFLAGS.DF is clear (Rust reference, `asm.rules.x86-df`).
#[cfg(target_arch = "x86_64")]
pub mod x86_64;

#[cfg(target_arch = "x86_64")]
pub use x86_64::{
    lemma_same_control_flags_preserves_df, lemma_with_alignment_check_preserves_df, ControlReg,
    Cpl, Cr0, Cr0Value, Cr1, Cr2, Cr3, Cr3Value, Cr4, Cr4Value, Cs, DescriptorTableValue, Ds,
    EferValue, Es, GdtrBaseLimit, Gs, IdtrBaseLimit, Msr, Pkru, Rax, Rflags, RflagsValue, Rsp,
    Ss, Xcr0,
};
