//! x86_64 four-level paging. The confidentiality bit is a parameter, not a
//! constant: on SEV-SNP the firmware reports which address bit encrypts a page,
//! so the type is generic over a marker that supplies it.

use super::pt_flags::PTEntryFlags;
use crate::structs::arch_contract::ArchPagingMeta;

/// Which address bit encrypts a page, as reported by the platform. Zero when
/// memory is not encrypted.
pub trait X86PagingParams: 'static {
    fn private_mask() -> usize;
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
