//! Tree lifecycle states and their ownership and reclamation rules.
//!
//! ```text
//! allocate / build
//!        |
//!        v
//!      Staged ----------- into_live() -----------> Live
//!        ^                                         |
//!        | synchronize old walks and caches        | unlink a child
//!        |                                         v
//!        +------------------------------------- Detached
//! ```
//!
//! The `Live -> Detached` transition applies to the removed child subtree;
//! its parent tree stays `Live`. Synchronization completes old hardware walks
//! and invalidates cached table pointers before the child becomes `Staged`.
//! A staged tree may be reclaimed or transferred to a live parent for publication.
//!
//! `into_live()` enables the live-access protocol; it does not load CR3 or
//! activate hardware. This diagram describes lifecycle, not root-entry ownership,
//! which is a separate policy concern.
//! CPU-local activation bindings live in `pagetable`. Both active and retired
//! controllers keep the `Live` tree state: switching one CPU away neither
//! detaches subtrees nor proves hardware quiescence.
//!
//! The level-erased public cleanup path is narrower:
//! `DetachedPageTable -> StagedPageTable -> drop`. That wrapper has no transition
//! back to `Live`.

use crate::structs::policy::{OwnedIndices, PagingOwnershipPolicy};

/// An unpublished or synchronized tree permitting exclusive access.
pub struct Staged;

/// An unlinked tree that old hardware walks may still reference.
/// Synchronization must complete before exclusive access or reclamation.
pub(crate) struct Detached;

/// A tree permitting atomic views and content-locked updates.
/// Enabling this state does not activate hardware.
pub(crate) struct Live;

/// Selects descendant ownership from the tree lifecycle.
pub(crate) trait TreeState {
    const RECLAIM_ON_DROP: bool;

    /// Returns whether the tree owns the subtree at this root index.
    fn owns_top_entry<S: PagingOwnershipPolicy>(index: usize) -> bool;
}

/// Permits page views and validation; detached trees must synchronize first.
pub(crate) trait AccessibleTreeState: TreeState {}

impl TreeState for Staged {
    const RECLAIM_ON_DROP: bool = true;

    fn owns_top_entry<S: PagingOwnershipPolicy>(_: usize) -> bool {
        true
    }
}

impl AccessibleTreeState for Staged {}

impl TreeState for Detached {
    const RECLAIM_ON_DROP: bool = false;

    fn owns_top_entry<S: PagingOwnershipPolicy>(_: usize) -> bool {
        true
    }
}

impl TreeState for Live {
    const RECLAIM_ON_DROP: bool = true;

    fn owns_top_entry<S: PagingOwnershipPolicy>(index: usize) -> bool {
        <S::Owned as OwnedIndices>::contains(index, index + 1)
    }
}

impl AccessibleTreeState for Live {}
