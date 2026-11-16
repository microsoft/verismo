//! Stable path for the target's tracked register state, whose definition lives
//! in `crate::arch`.
#[cfg(target_arch = "x86_64")]
pub use crate::arch::x86_64::state::RegisterState;
