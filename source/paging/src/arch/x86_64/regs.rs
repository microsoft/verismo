//! Privileged x86-64 root-register access and CPU-local activation encoding.
pub use machine_model::arch::x86_64::{Cr3, Cr3Value, Cr4, Cr4Value};

use super::{X86_64Paging, X86_64PagingParams};
use crate::address::{Address, PhysAddr};
use crate::pagetable::RootRegisterAccess;
use crate::structs::{ArchPagingMeta, LevelSpec, PageLevel, PagingError};

/// Computes CR3 flags using a supplied CR4 value and root level.
///
/// With PCIDE enabled, PWT/PCD must be clear; otherwise PCID and no-flush
/// must be zero/false. The level must match LA57. No hardware is accessed.
/// `no_flush` requires valid retained translations for this PCID and root.
pub fn cr3_flags(
    cr4: Cr4Value,
    level: PageLevel,
    pcid: u16,
    no_flush: bool,
    write_through: bool,
    cache_disable: bool,
) -> Result<Cr3Value, PagingError> {
    let la57 = cr4.contains(Cr4Value::LA57);
    if !matches!((level, la57), (PageLevel::Level3, false) | (PageLevel::Level4, true)) {
        return Err(PagingError::InvalidLevel);
    }
    if cr4.contains(Cr4Value::PCIDE) {
        if write_through || cache_disable || pcid as u64 > Cr3Value::PCID_MASK.bits() {
            return Err(PagingError::InvalidFlags);
        }
        Ok(Cr3Value::from_bits_retain(
            (pcid as u64) | if no_flush { Cr3Value::NO_FLUSH.bits() } else { 0 },
        ))
    } else {
        if pcid != 0 || no_flush {
            return Err(PagingError::InvalidFlags);
        }
        let pwt = if write_through { Cr3Value::PWT.bits() } else { 0 };
        let pcd = if cache_disable { Cr3Value::PCD.bits() } else { 0 };
        Ok(Cr3Value::from_bits_retain(pwt | pcd))
    }
}

// SAFETY: CR3 writes are CPU-local and order root publication. All rejection
// paths precede the write; reads strip flags and confidentiality tags.
unsafe impl<P: X86_64PagingParams> RootRegisterAccess for X86_64Paging<P> {
    unsafe fn read_root_pa() -> PhysAddr {
        Self::decode_physical_address(Cr3.read().bits() as usize)
    }

    unsafe fn store_root_pa<L: LevelSpec>(root: PhysAddr, flags: usize) -> Result<(), PagingError> {
        if root != Self::decode_physical_address(root.bits()) || !root.is_aligned(4096) {
            return Err(PagingError::InvalidAddress);
        }
        let value = Self::make_private_address(root).bits() | flags;
        Cr3.write(Cr3Value::from_bits_retain(value as u64));
        Ok(())
    }
}
