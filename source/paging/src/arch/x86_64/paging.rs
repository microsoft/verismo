//! x86_64 paging with platform-supplied confidentiality tags and TLB hooks.
//! Firmware determines the SEV-SNP encryption bit; other platforms may instead
//! encode sharing with a set bit.

use super::pt_flags::PTEntryFlags;
use super::tlb::{FlushScope, X86TlbFlushTok};
use crate::structs::arch_contract::ArchPagingMeta;
use crate::structs::level::PageLevel;

/// Platform tag encoding, allowed request flags, and translation invalidation.
///
/// # Safety
///
/// `private_mask()` and `shared_mask()` must be disjoint, page-aligned subsets
/// of the x86-64 PTE address field. Every set bit must be reserved for the
/// stated confidentiality tag rather than a physical-address bit.
/// `supported_flags()` must contain only architecturally valid flag bits and
/// must not overlap the PTE address field.
///
/// Every flush hook must invalidate at least the translations described by
/// `scope`, with `All` covering all translations and `Range` covering the
/// entire half-open range at its stated level. `sync` hooks must cover every
/// processor that could use the mapping; `percpu` hooks must cover the current
/// processor. Hooks named `global` must include global translations, while
/// `ignore_global` hooks may omit them. All hooks must complete before
/// returning and must not re-enter the content-lock domain or wait for software
/// that needs its write guard.
pub unsafe trait X86PagingParams:
    'static + Copy + core::fmt::Debug + PartialEq + Eq
{
    fn private_mask() -> usize;

    /// A set-bit shared tag, where sharing is not just absence of the private tag.
    fn shared_mask() -> usize {
        0
    }

    fn supported_flags() -> PTEntryFlags;

    /// Invalidate `scope` on every processor, including global pages.
    fn flush_tlb_global_sync(scope: FlushScope);

    /// Invalidate `scope` on this processor only, including global pages.
    fn flush_tlb_global_percpu(scope: FlushScope) {
        Self::flush_tlb_global_sync(scope)
    }

    /// Invalidate `scope` on every processor, ignoring global pages.
    fn flush_tlb_ignore_global_sync(scope: FlushScope) {
        Self::flush_tlb_global_sync(scope)
    }

    /// Invalidate `scope` on this processor only, ignoring global pages.
    fn flush_tlb_ignore_global_percpu(scope: FlushScope) {
        Self::flush_tlb_global_percpu(scope)
    }
}

/// x86_64 paging with 4 KiB pages and 512-entry tables.
pub struct X86Paging<P: X86PagingParams> {
    dummy: core::marker::PhantomData<P>,
}

impl<P: X86PagingParams> Clone for X86Paging<P> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P: X86PagingParams> Copy for X86Paging<P> {}

impl<P: X86PagingParams> ArchPagingMeta for X86Paging<P> {
    type PTFlags = PTEntryFlags;

    type TlbFlushTok = X86TlbFlushTok<P>;

    #[inline(always)]
    fn private_pte_mask() -> usize {
        P::private_mask()
    }

    #[inline(always)]
    fn shared_pte_mask() -> usize {
        P::shared_mask()
    }

    #[inline(always)]
    fn address_mask() -> usize {
        0x000f_ffff_ffff_f000
    }

    fn split_leaf_attributes(entry: usize, level: PageLevel) -> usize {
        let pat = (entry >> 12) & 1;
        pat << if level == PageLevel::Level1 { 7 } else { 12 }
    }

    fn leaf_attribute_mask(level: PageLevel) -> usize {
        1 << if level.is_leaf() { 7 } else { 12 }
    }

    fn accessed_dirty_mask() -> usize {
        (PTEntryFlags::ACCESSED | PTEntryFlags::DIRTY).bits()
    }

    fn requires_break_before_make(_old: usize, _new: usize, _level: PageLevel) -> bool {
        false
    }

    fn supported_flags() -> Self::PTFlags {
        P::supported_flags()
    }
}
