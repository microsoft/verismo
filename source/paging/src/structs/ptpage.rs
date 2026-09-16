//! Page-table storage, lifetime-bound views, and unpublished tree ownership.

mod node;
mod node_pointer;
mod tree;

pub(crate) use node::LeafUpdate;
pub use node::{MapSpec, Mapping, PTPage, Translation};
pub(crate) use node_pointer::PTPagePointer;
#[cfg(feature = "concurrent")]
pub(crate) use node_pointer::WalkResult;
pub(crate) use tree::{free_children, reclaim_path, reclaim_range, PTPageTree};
