//! Page-table storage, lifetime-bound views, and unpublished tree ownership.

mod node;
mod node_pointer;
mod tree;

pub(crate) use node::FlushFootprint;
pub use node::{Mapping, PTPage, Translation};
pub(crate) use node_pointer::PTPagePointer;
pub(crate) use tree::{free_children, reclaim_path, reclaim_range, PTPageTree};
