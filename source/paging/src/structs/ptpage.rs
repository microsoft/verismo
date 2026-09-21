//! Page-table storage, lifetime-bound views, and unpublished tree ownership.

mod node;
mod node_pointer;
mod tree;

pub(crate) use node::FlushFootprint;
pub use node::{Mapping, PTPage, Translation};
pub(crate) use node_pointer::PTPagePointer;
pub use node_pointer::WalkResult;
pub(crate) use tree::{reclaim_path, reclaim_range, Live, PTPageTree};
