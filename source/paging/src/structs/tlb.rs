//! Translation invalidation. Page-size transitions flush synchronously before
//! publishing replacements; [`MayNeedFlush`] records any remaining obligation
//! for the caller to discharge.
use crate::structs::address::{VirtAddr, LOW_CANONICAL_END};
use crate::structs::level::PageLevel;
use crate::structs::sizes::PAGE_SIZE;

/// An opaque description of translations to invalidate.
///
/// Hooks must complete invalidation before returning. Publication barriers call
/// them with the content write guard held: they must not re-enter that domain
/// or wait for software that needs the guard. Walks remain lock-free.
pub trait TlbFlush: Sized {
    /// A token covering `[start, end)`, whose mapping changed at `level`.
    fn range(start: VirtAddr, end: VirtAddr, level: PageLevel) -> Self;

    /// A token standing for "flush everything", used when the footprint of a
    /// mutation is unknown or when merging two disjoint tokens.
    fn all() -> Self;

    /// Flush on all processors, including global pages, waiting for completion.
    fn flush_tlb_global_sync(self);

    /// A token covering both. Widening to [`TlbFlush::all`] is always correct;
    /// override to keep range precision where the architecture allows it.
    fn and(self, _: Self) -> Self {
        Self::all()
    }

    /// Complete a flush on this processor only, including global pages.
    fn flush_tlb_global_percpu(self) {
        self.flush_tlb_global_sync()
    }

    /// Flush on all processors, ignoring global pages.
    fn flush_tlb_ignore_global_sync(self) {
        self.flush_tlb_global_sync()
    }

    /// Flush on this processor only, ignoring global pages.
    fn flush_tlb_ignore_global_percpu(self) {
        self.flush_tlb_global_percpu()
    }
}

/// A caller may still owe a TLB invalidation for the mapping it just changed.
///
/// `#[must_use]` is a lint, not a proof: it does not guarantee a flush happens,
/// only that dropping the obligation has to be written down.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[must_use = "this page-table mutation may have invalidated a live TLB entry; \
flush the affected page or discharge the obligation with `.ignore()`"]
pub struct MayNeedFlush<T: TlbFlush> {
    tok: Option<T>,
}

impl<T: TlbFlush> MayNeedFlush<T> {
    /// The pending token, if a flush is still owed.
    pub fn scope(&self) -> &Option<T> {
        &self.tok
    }

    /// An obligation to flush the single page at `vaddr` mapped at `level`.
    pub fn new(vaddr: VirtAddr, level: PageLevel) -> Self {
        let start = vaddr.as_usize() & !(level.size() - 1);
        match start.checked_add(level.size()) {
            Some(end) if VirtAddr::from(end).as_usize() == end => {
                Self::new_range(start.into(), end.into(), level)
            }
            _ => Self::all(),
        }
    }

    /// An optimized obligation for one configured minimum-size page.
    pub(crate) fn new_small(vaddr: VirtAddr) -> Self {
        let start = vaddr.as_usize() & !(PAGE_SIZE - 1);
        if start == LOW_CANONICAL_END - PAGE_SIZE {
            return Self::all();
        }
        match start.checked_add(PAGE_SIZE) {
            Some(end) => {
                Self::new_range(VirtAddr::new(start), VirtAddr::new(end), PageLevel::Level0)
            }
            None => Self::all(),
        }
    }

    /// An obligation to flush `[start, end)`, every entry of which was mapped
    /// at `level`. For callers that edit entries themselves and must therefore
    /// vouch for the range.
    pub fn new_range(start: VirtAddr, end: VirtAddr, level: PageLevel) -> Self {
        MayNeedFlush { tok: Some(T::range(start, end, level)) }
    }

    /// A discharged token: the mutation left no live translation stale.
    pub fn none() -> Self {
        MayNeedFlush { tok: None }
    }

    /// An obligation to flush the whole TLB.
    pub fn all() -> Self {
        MayNeedFlush { tok: Some(T::all()) }
    }

    /// One obligation covering both; discharged only if both inputs are.
    pub fn and(self, other: Self) -> Self {
        match (self.tok, other.tok) {
            (Some(a), Some(b)) => MayNeedFlush { tok: Some(a.and(b)) },
            (Some(tok), None) | (None, Some(tok)) => MayNeedFlush { tok: Some(tok) },
            (None, None) => MayNeedFlush { tok: None },
        }
    }

    /// Whether a flush is still owed.
    pub fn is_pending(&self) -> bool {
        self.tok.is_some()
    }

    /// Discharge by flushing on all processors, ignoring global pages.
    ///
    /// # Panics
    /// Panics if the obligation is already discharged.
    pub fn flush_tlb_ignore_global_sync(self) {
        self.tok.unwrap().flush_tlb_ignore_global_sync();
    }

    /// Discharge by flushing the affected translations on all processors,
    /// including global pages.
    ///
    /// # Panics
    /// Panics if the obligation is already discharged.
    pub fn flush_tlb_global_sync(self) {
        self.tok.unwrap().flush_tlb_global_sync();
    }

    /// Discharge by flushing the affected translations on this processor only,
    /// including global pages. Correct only if the changed mapping cannot be
    /// live elsewhere.
    ///
    /// # Panics
    /// Panics if the obligation is already discharged.
    pub fn flush_tlb_global_percpu(self) {
        self.tok.unwrap().flush_tlb_global_percpu();
    }

    /// Discharge by flushing the non-global entries on this processor only.
    ///
    /// # Panics
    /// Panics if the obligation is already discharged.
    pub fn flush_tlb_percpu(self) {
        self.tok.unwrap().flush_tlb_ignore_global_percpu();
    }

    /// Discharge without flushing.
    ///
    /// # Safety
    /// No processor may hold a stale translation for the changed mapping.
    pub unsafe fn ignore(self) {}

    /// Assert that nothing is owed.
    ///
    /// # Panics
    /// Panics if a flush is still pending.
    pub fn expect_no_flush(self) {
        assert!(self.tok.is_none());
    }
}
