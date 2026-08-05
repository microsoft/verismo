//! **The specification.** Two files, to be read and believed.
//!
//! Both are trusted spec: nothing checks that they say the right thing. The failure mode is
//! vacuity, not unsoundness -- a model whose `wf_payload` is `true` satisfies every obligation
//! here and learns nothing from any of them, and a guarantee is only worth what its `ensures`
//! clause says. So both files are kept short, bodiless, and free of tokens, invariants and
//! pointers, to be read end to end. Together they are the whole public API.
/// **Trusted spec.** What a client supplies: the model traits, with no bodies.
pub mod model;

/// **Trusted spec.** What the crate guarantees back, with no bodies.
pub mod contract;

pub use contract::*;
pub use model::*;
