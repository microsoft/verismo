//! Telling the processor that a translation has changed. The page table changes
//! memory; the TLB is not memory. [`MayNeedFlush`] is `#[must_use]`, so
//! ignoring a stale translation has to be written down.
use crate::structs::os_contract::PagingHandler;

/// A range of addresses whose cached translations may now be wrong. An empty
/// range means nothing changed.
#[must_use]
pub struct MayNeedFlush {
    start: usize,
    end: usize,
}

impl MayNeedFlush {
    /// Nothing changed, so nothing is stale.
    pub fn none() -> Self {
        MayNeedFlush { start: 0, end: 0 }
    }

    /// The translations of `[start, end)` may be stale.
    pub fn range(start: usize, end: usize) -> Self {
        MayNeedFlush { start, end }
    }

    /// The addresses that may be stale, as a half-open range.
    pub fn addresses(&self) -> (usize, usize) {
        (self.start, self.end)
    }

    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    /// Hands the range to the OS to invalidate.
    pub fn flush<P: PagingHandler>(self) {
        if self.start < self.end {
            P::flush_range(self.start, self.end);
        }
    }

    /// Deliberately leaves the stale translations alone. Correct when the table
    /// is not installed on any processor, and wrong otherwise; spelling it out
    /// is the point.
    pub fn ignore(self) {}
}
