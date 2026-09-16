//! Mutation authority and ownership of subtrees below an owned root.

use core::marker::PhantomData;
use core::ops::Range;

use crate::structs::address::{Address, VirtAddr, LOW_CANONICAL_END};
use crate::structs::level::PageLevel;
use crate::structs::os_contract::PagingError;
use crate::structs::sizes::entry_index;
use crate::structs::sizes::ENTRY_COUNT;

mod sealed {
    /// Prevents downstream crates from defining paging ownership policies.
    pub trait Sealed {}
}

/// Authorizes address mutations and selects which top-level subtrees are owned.
pub trait PagingOwnershipPolicy: sealed::Sealed {
    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError>;
    fn check_range(
        &self,
        root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError>;
    fn owns_top_entry(&self, index: usize) -> bool;
}

/// Privileged access to the whole tree; every attached subtree is owned.
#[derive(Clone, Copy, Debug, Default)]
pub struct KernelPolicy;

/// Zero-sized policy reserving `START..END` for immutable, non-owned kernel slots.
#[derive(Debug)]
pub struct UserPolicy<'kernel, const START: usize, const END: usize> {
    kernel: PhantomData<&'kernel ()>,
}

impl<const START: usize, const END: usize> UserPolicy<'_, START, END> {
    pub(crate) fn new() -> Self {
        assert!(START <= END && END <= ENTRY_COUNT);
        Self { kernel: PhantomData }
    }

    pub fn kernel_top(&self) -> Range<usize> {
        START..END
    }

    fn overlaps(&self, start: usize, end: usize) -> bool {
        start < END && START < end
    }

    fn check_segment(&self, root: PageLevel, first: usize, last: usize) -> Result<(), PagingError> {
        let first_page = first / root.size();
        let last_page = last / root.size();
        let first_index = first_page % ENTRY_COUNT;
        let last_index = last_page % ENTRY_COUNT;
        let denied = last_page - first_page >= ENTRY_COUNT
            || if first_index <= last_index {
                self.overlaps(first_index, last_index + 1)
            } else {
                self.overlaps(first_index, ENTRY_COUNT) || self.overlaps(0, last_index + 1)
            };
        if denied {
            Err(PagingError::PermissionDenied)
        } else {
            Ok(())
        }
    }
}

impl sealed::Sealed for KernelPolicy {}
impl<const START: usize, const END: usize> sealed::Sealed for UserPolicy<'_, START, END> {}

impl PagingOwnershipPolicy for KernelPolicy {
    fn check_address(&self, _root: PageLevel, _address: VirtAddr) -> Result<(), PagingError> {
        Ok(())
    }

    fn check_range(
        &self,
        _root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError> {
        if start > end {
            Err(PagingError::InvalidRange)
        } else {
            Ok(())
        }
    }

    fn owns_top_entry(&self, index: usize) -> bool {
        assert!(index < ENTRY_COUNT);
        true
    }
}

impl<const START: usize, const END: usize> PagingOwnershipPolicy for UserPolicy<'_, START, END> {
    fn check_address(&self, root: PageLevel, address: VirtAddr) -> Result<(), PagingError> {
        if self.kernel_top().contains(&entry_index(address, root)) {
            Err(PagingError::PermissionDenied)
        } else {
            Ok(())
        }
    }

    fn check_range(
        &self,
        root: PageLevel,
        start: VirtAddr,
        end: VirtAddr,
    ) -> Result<(), PagingError> {
        if start > end {
            return Err(PagingError::InvalidRange);
        }
        if start == end || START == END {
            return Ok(());
        }
        let last = VirtAddr::from(end.bits() - 1).bits();
        if start.bits() < LOW_CANONICAL_END && last >= LOW_CANONICAL_END {
            self.check_segment(root, start.bits(), LOW_CANONICAL_END - 1)?;
            self.check_segment(root, VirtAddr::from(LOW_CANONICAL_END).bits(), last)
        } else {
            self.check_segment(root, start.bits(), last)
        }
    }

    fn owns_top_entry(&self, index: usize) -> bool {
        assert!(index < ENTRY_COUNT);
        !self.kernel_top().contains(&index)
    }
}

#[cfg(test)]
#[path = "../../tests/unit/policy.rs"]
mod tests;
