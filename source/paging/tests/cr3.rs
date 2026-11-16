//! Ensures tagged addresses retain leaf attributes while decoding physical roots.
use paging::{
    address::{Address, PhysAddr},
    arch::x86_64::{Cr3Value, FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams},
    structs::{ArchPagingMeta, PTEntry, PageLevel},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Tagged;

// SAFETY: tests only decode values; no hardware register is accessed.
unsafe impl X86_64PagingParams for Tagged {
    fn private_mask() -> usize {
        1 << 51
    }
    fn shared_mask() -> usize {
        1 << 50
    }
    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }
    fn flush_tlb_global_sync(_: FlushScope) {}
}

type Arch = X86_64Paging<Tagged>;

#[test]
fn root_reads_strip_register_flags_pcid_and_confidentiality_tags() {
    for value in [
        0x2018usize,
        (1usize << 51) | 0x2fff,
        Cr3Value::NO_FLUSH.bits() as usize | (1usize << 50) | 0x2fff,
    ] {
        assert_eq!(Arch::decode_physical_address(value), PhysAddr::from(0x2000usize));
    }
}

#[test]
fn common_decoding_preserves_tagged_fields_and_level_specific_leaf_attributes() {
    let tags = (1usize << 51) | (1usize << 50);
    let entry = PTEntry::<Arch>::new(
        PhysAddr::from(tags | 0x2000),
        PTEntryFlags::from_bits_retain(Cr3Value::NO_FLUSH.bits() as usize | 0x18),
    );
    assert_eq!(entry.address(), Arch::decode_physical_address(entry.raw()).bits());
    assert_eq!(entry.address(), 0x2000);
    assert_eq!(entry.paddr_field(), tags | 0x2000);
    assert_eq!(entry.page_frame(), (1usize << 50) | 0x2000);

    let huge = PTEntry::<Arch>::new(
        PhysAddr::from(tags | 0x201000),
        PTEntryFlags::PRESENT | PTEntryFlags::HUGE,
    );
    assert_eq!(Arch::decode_physical_address(huge.raw()), PhysAddr::from(0x201000usize));
    assert_eq!(huge.address(), 0x201000);
    assert_eq!(huge.leaf_address(PageLevel::Level1), PhysAddr::from(0x200000usize));
}
