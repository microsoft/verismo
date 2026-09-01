mod control;
mod flags;
mod model_tests;
mod ops;
mod spec;
pub mod state;
pub use control::ControlReg;
pub use flags::{Cr0Value, Cr3Value, Cr4Value, EferValue, RflagsValue};
pub use spec::{
    Cr0, Cr1, Cr2, Cr3, Cr4, Cs, DescriptorTableValue, Ds, Es, GdtrBaseLimit, Gs, IdtrBaseLimit,
    Msr, Pkru, Rax, Rflags, Rsp, Ss, Xcr0,
};

// Ghost-only: `verus!` erases spec and proof functions, so a plain `cargo build`
// has nothing to re-export.
#[cfg(verus_only)]
pub use flags::{lemma_same_control_flags_preserves_df, lemma_with_alignment_check_preserves_df};
#[cfg(verus_only)]
pub use spec::cpl;
