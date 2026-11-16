//! Page-table storage, lifetime-bound views, and unpublished tree ownership.
mod node;
mod node_ref;
mod state;
mod tree;

pub(crate) use node::FlushFootprint;
pub use node::{PTPage, Translation};
pub use node_ref::WalkLevel;
pub use node_ref::WalkResult;
pub(crate) use node_ref::{PTPageMutRef, PTPageRef, WalkLevelImpl};
pub(crate) use state::Live;
pub use state::Staged;
pub use tree::{DetachedPageTable, PTPageTree, StagedPageTable};

/// An unlinked child tree whose ownership can be transferred to a parent.
pub type OwnedSubtree<A, P, L> = PTPageTree<A, P, L>;
