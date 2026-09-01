//! Ghost-only specifications: trait impls that say what this crate's types mean
//! rather than what they do.
//!
//! `external` and `nonnull` are vendored from COCONUT-SVSM's `verify_external`
//! crate, reduced to what this crate uses, and specify types we do not own.
//! The rest specify our own types, and live apart from them because Verus
//! treats an impl block as one recursion node: an impl that names another is
//! grouped with it and cannot see its definitions.
pub mod boot_states;
pub mod concurrent_entry;
#[cfg(verus_only)]
pub mod entry;
// Vendored specs for types we do not own; nothing but ghost, and they name
// vstd items that a plain `cargo build` erases.
#[cfg(verus_only)]
pub mod external;
#[cfg(verus_only)]
pub mod nonnull;
pub mod page_table;
pub mod points_to;
pub mod points_to_axiom;
