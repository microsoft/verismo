//! The x86_64 flush token: what a page-table mutation asks the OS to
//! invalidate. The crate builds these; discharging them means IPIs and `invlpg`
//! and so belongs to the embedder, which supplies them through
//! [`X86PagingParams`].
use crate::structs::address::VirtAddr;
use crate::structs::level::PageLevel;
use crate::structs::tlb::TlbFlush;

use super::paging::X86PagingParams;

/// What a flush must cover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlushScope {
    /// Every cached translation.
    All,
    /// The translations of `[start, end)`, mapped at `level`.
    Range { start: VirtAddr, end: VirtAddr, level: PageLevel },
}

/// A pending x86_64 invalidation, discharged through the embedder's hooks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct X86TlbFlushTok<P: X86PagingParams> {
    scope: FlushScope,
    dummy: core::marker::PhantomData<P>,
}

impl<P: X86PagingParams> X86TlbFlushTok<P> {
    pub fn scope(&self) -> FlushScope {
        self.scope
    }

    fn new(scope: FlushScope) -> Self {
        Self { scope, dummy: core::marker::PhantomData }
    }
}

impl<P: X86PagingParams> TlbFlush for X86TlbFlushTok<P> {
    fn range(start: VirtAddr, end: VirtAddr, level: PageLevel) -> Self {
        Self::new(FlushScope::Range { start, end, level })
    }

    fn all() -> Self {
        Self::new(FlushScope::All)
    }

    /// Two adjacent ranges of the same page size merge; anything else widens to
    /// the whole TLB, which is always correct and never cheaper than it has to
    /// be for the single-range case.
    fn and(self, other: Self) -> Self {
        match (self.scope, other.scope) {
            (
                FlushScope::Range { start: s1, end: e1, level: l1 },
                FlushScope::Range { start: s2, end: e2, level: l2 },
            ) if l1 == l2 && (s2 <= e1 && s1 <= e2) => Self::range(
                if s1 < s2 { s1 } else { s2 },
                if e1 > e2 { e1 } else { e2 },
                l1,
            ),
            _ => Self::all(),
        }
    }

    fn flush_tlb_global_sync(self) {
        P::flush_tlb_global_sync(self.scope)
    }

    fn flush_tlb_global_percpu(self) {
        P::flush_tlb_global_percpu(self.scope)
    }

    fn flush_tlb_ignore_global_sync(self) {
        P::flush_tlb_ignore_global_sync(self.scope)
    }

    fn flush_tlb_ignore_global_percpu(self) {
        P::flush_tlb_ignore_global_percpu(self.scope)
    }
}
