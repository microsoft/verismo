//! Ensures CR3 flags and tagged addresses are encoded and decoded correctly without privileged host instructions.
use paging::{
    address::{Address, PhysAddr},
    arch::x86_64::{
        cr3_flags, Cr3Value, Cr4Value, FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams,
    },
    structs::{ArchPagingMeta, PTEntry, PageLevel, PagingError},
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
fn cr3_flags_encodes_each_legacy_cache_flag_and_zero_pcid() {
    for (pwt, pcd, expected) in [
        (false, false, Cr3Value::empty()),
        (true, false, Cr3Value::PWT),
        (false, true, Cr3Value::PCD),
        (true, true, Cr3Value::PWT | Cr3Value::PCD),
    ] {
        assert_eq!(
            cr3_flags(Cr4Value::empty(), PageLevel::Level3, 0, false, pwt, pcd),
            Ok(expected),
        );
    }
    assert_eq!(
        cr3_flags(Cr4Value::PCIDE, PageLevel::Level3, 0, false, false, false),
        Ok(Cr3Value::empty()),
    );
}

#[test]
fn cr3_flags_selects_fields_using_the_supplied_mode() {
    assert_eq!(
        cr3_flags(Cr4Value::empty(), PageLevel::Level3, 0, false, true, true).unwrap().bits(),
        0x18,
    );
    for (cr4, level) in [
        (Cr4Value::PCIDE, PageLevel::Level3),
        (Cr4Value::PCIDE | Cr4Value::LA57, PageLevel::Level4),
    ] {
        assert_eq!(
            cr3_flags(cr4, level, 4095, true, false, false).unwrap().bits(),
            (1u64 << 63) | 0xfff,
        );
    }
    assert_eq!(
        cr3_flags(Cr4Value::LA57, PageLevel::Level4, 0, false, false, false),
        Ok(Cr3Value::empty()),
    );
}

#[test]
fn cr3_flags_rejects_mismatched_levels_and_incompatible_fields() {
    for (cr4, level) in [
        (Cr4Value::empty(), PageLevel::Level0),
        (Cr4Value::empty(), PageLevel::Level1),
        (Cr4Value::empty(), PageLevel::Level2),
        (Cr4Value::empty(), PageLevel::Level4),
        (Cr4Value::LA57, PageLevel::Level3),
    ] {
        assert_eq!(cr3_flags(cr4, level, 0, false, false, false), Err(PagingError::InvalidLevel),);
    }
    for (cr4, pcid, no_flush, pwt, pcd) in [
        (Cr4Value::empty(), 1, false, false, false),
        (Cr4Value::empty(), 0, true, false, false),
        (Cr4Value::PCIDE, 0, false, true, false),
        (Cr4Value::PCIDE, 0, false, false, true),
        (Cr4Value::PCIDE, 4096, false, false, false),
        (Cr4Value::PCIDE, u16::MAX, true, false, false),
    ] {
        assert_eq!(
            cr3_flags(cr4, PageLevel::Level3, pcid, no_flush, pwt, pcd),
            Err(PagingError::InvalidFlags),
        );
    }
}

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
