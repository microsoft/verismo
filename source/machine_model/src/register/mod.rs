pub(crate) mod points_to;
pub(crate) mod reg_trait;
pub use points_to::{AsmRegisterPointsTo, RustRegisterPointsTo};
pub use reg_trait::ReadableReg;
pub use reg_trait::RegSpec;
