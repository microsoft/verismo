//! Ghost-only specifications: trait impls that say what this crate's types mean
//! rather than what they do.
//!
//! `external` is vendored from COCONUT-SVSM's `verify_external` crate, reduced
//! to what this crate uses, and specifies types we do not own. Specs of our own
//! types live apart from them because Verus treats an impl block as one
//! recursion node: an impl that names another is grouped with it and cannot see
//! its definitions.
//!
#[cfg(verus_only)]
pub mod external;
