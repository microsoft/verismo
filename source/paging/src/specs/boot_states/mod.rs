//! The permissions an OS holds before it has mapped anything.
//!
//! One module per way the firmware can leave the page table behind, since what
//! the OS starts with is decided by how it was handed over.
/// A handover whose root page table is reached through a self map.
pub mod self_mapped;
