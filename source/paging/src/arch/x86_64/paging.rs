//! x86_64 four-level paging. The confidentiality bit is a parameter, not a
//! constant: on SEV-SNP the firmware reports which address bit encrypts a page,
//! so the type is generic over a marker that supplies it.

use super::pt_flags::PTEntryFlags;
use super::tlb::{FlushScope, X86TlbFlushTok};
use crate::structs::arch_contract::ArchPagingMeta;

/// What the platform tells the page table: which address bit encrypts a page
/// (zero when memory is not encrypted), and how to invalidate translations.
pub trait X86PagingParams: 'static + Copy + core::fmt::Debug + PartialEq + Eq {
    fn private_mask() -> usize;

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

    fn private_pte_mask() -> usize {
        P::private_mask()
    }

    /// Nothing is shared unless the embedder says so; on SEV-SNP the shared bit
    /// is the absence of the private one.
    fn shared_pte_mask() -> usize {
        0
    }

    fn address_mask() -> usize {
        0x000f_ffff_ffff_f000
    }

    fn supported_flags() -> Self::PTFlags {
        PTEntryFlags::all()
    }
}
