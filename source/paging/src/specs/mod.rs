//! Ghost-only specifications: trait impls that say what this crate's types mean
//! rather than what they do.
//!
//! `external` is vendored from COCONUT-SVSM's `verify_external` crate, reduced
//! to what this crate uses, and specifies types we do not own. Specs of our own
//! types live apart from them because Verus treats an impl block as one
//! recursion node: an impl that names another is grouped with it and cannot see
//! its definitions.
//!
//! The rest of this directory -- `boot_states`, `entry`, `nonnull`,
//! `page_table`, `points_to`, `points_to_axiom`, `slot` -- specifies the page
//! table as it was before the rewrite, and is left out of the module tree until
//! it is ported to the one that replaced it.
#[cfg(verus_only)]
pub mod external;
