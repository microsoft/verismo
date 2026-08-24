//! Telling the processor that a translation has changed.
//!
//! The page table changes memory; the TLB is not memory, and nothing in the
//! tree can invalidate it. Which processors are walking this table, and whether
//! reaching them needs an IPI, is the OS's to know -- so the crate does two
//! things and no more: it says *which addresses* may be stale, and it makes
//! that hard to forget.
//!
//! [`MayNeedFlush`] is `#[must_use]`, so an operation that may have left a
//! stale translation behind hands back a value the caller cannot silently
//! drop. Ignoring it is possible, but has to be written down --
//! [`MayNeedFlush::ignore`] -- which is the difference between a decision and
//! an oversight.
use builtin_macros::{verus_spec, verus_verify};

use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::os_contract::OSPagingContract;

/// A range of addresses whose cached translations may now be wrong.
///
/// Returned by every operation that can invalidate one. An empty range means
/// nothing changed -- an unmap that found nothing mapped, say -- and flushing
/// it does nothing.
#[must_use]
#[verus_verify]
pub struct MayNeedFlush {
    start: usize,
    end: usize,
}

#[verus_verify]
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

    /// Whether anything actually needs flushing.
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    /// Hands the range to the OS to invalidate.
    pub fn flush<A: ArchPagingMeta, P: OSPagingContract<A>>(self) {
        if self.start < self.end {
            P::flush_range(self.start, self.end);
        }
    }

    /// Deliberately leaves the stale translations alone.
    ///
    /// Correct when the table is not installed on any processor -- during
    /// construction, or after the address space has been torn down -- and
    /// wrong otherwise. Spelling it out is the point.
    pub fn ignore(self) {}
}
