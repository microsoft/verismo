use vstd::slice::slice_index_get;

use super::*;
use crate::arch::addr_s::VM_MEM_SIZE;
use crate::debug::VPrint;
use crate::registers::SnpCore;
use crate::snp::SnpCoreConsole;

verus! {

#[verifier::publish]
pub const E820_TYPE_RAM: u32 = 1;

#[verifier::publish]
pub const E820_TYPE_RSVD: u32 = 2;

#[verifier::publish]
pub const E820_TYPE_ACPI: u32 = 3;

#[verifier::publish]
pub const E820_TYPE_READONLY: u32 = 3;

#[verifier::publish]
pub const E820_MAX_LEN: usize = 128;

#[verifier::publish]
pub const VERISMO_DYNAMIC_MEM_MAX: usize = 0x10000;

pub type E820Table = Array<E820Entry, E820_MAX_LEN>;

} // verus!
verismo_simple! {
#[repr(C, packed)]
#[derive(VClone, Copy)]
pub struct E820Entry {
    pub addr: u64,
    pub size: u64,
    pub memty: u32,
}
}

verus! {

impl VPrint for E820Entry {
    #[verifier(inline)]
    open spec fn early_print_requires(&self) -> bool {
        self.is_constant()
    }

    fn early_print2(
        &self,
        Tracked(snpcore): Tracked<&mut crate::registers::SnpCore>,
        Tracked(console): Tracked<SnpPointsToRaw>,
    ) -> (newconsole: Tracked<SnpPointsToRaw>) {
        let addr = self.addr;
        let size = self.size;
        let memty = self.memty;
        ((addr, size), memty).early_print2(Tracked(snpcore), Tracked(console))
    }
}

impl MemRangeInterface for E820Entry {
    #[verifier(inline)]
    open spec fn self_wf(&self) -> bool {
        self.wf()
    }

    #[verifier(inline)]
    open spec fn real_wf(r: (usize_s, usize_s)) -> bool {
        r.self_wf()
    }

    proof fn proof_constant_real_wf(r: (usize_s, usize_s)) {
    }

    open spec fn spec_real_range(&self) -> (usize_s, usize_s) {
        (self.addr.vspec_cast_to(), self.size.vspec_cast_to())
    }

    #[inline]
    fn real_range(&self) -> (usize_s, usize_s) {
        (self.addr.into(), self.size.into())
    }

    open spec fn spec_set_range(self, r: (usize_s, usize_s)) -> Self {
        E820Entry { addr: r.0.vspec_cast_to(), size: r.1.vspec_cast_to(), memty: self.memty }
    }

    fn update_range(&mut self, r: (usize_s, usize_s)) {
        let ghost oldself = *self;
        self.addr = r.0.into();
        self.size = r.1.into();
        proof {
            proof_sectype_cast_eq::<usize, u64, ()>(r.0);
            proof_sectype_cast_eq::<usize, u64, ()>(r.1);
            assert(oldself.spec_set_range(r) === E820Entry {
                addr: r.0.vspec_cast_to(),
                size: r.1.vspec_cast_to(),
                memty: self.memty,
            });
            // BUG(verus):
            assume(oldself.spec_set_range(r) === *self);
        }
    }

    open spec fn spec_end_max() -> usize {
        VM_MEM_SIZE
    }

    #[inline]
    fn end_max() -> usize_s {
        VM_MEM_SIZE.into()
    }
}

} // verus!
verismo_simple! {
impl E820Entry {
    #[verifier(inline)]
    pub open spec fn spec_aligned_end(&self) -> int {
        self.spec_aligned_range().end()
    }
}

#[verifier(inline)]
pub open spec fn e820_disjoint(e820: Seq<E820Entry>, r: (int, nat)) -> bool {
    ranges_disjoint(e820.to_valid_ranges(), r)
    //forall |e| e820.contains(e) ==> range_disjoint_(r, e.spec_range())
}

pub open spec fn e820_align_include(e820: Set<E820Entry>, r: (int, nat)) -> bool {
    exists |e| e820.contains(e) && inside_range(r, e.spec_aligned_range())
}

pub open spec fn e820_align_available_include(e820: Set<E820Entry>, r: (int, nat)) -> bool {
    exists |e| e820.contains(e) && inside_range(r, e.spec_aligned_range()) && e.memty != E820_TYPE_RSVD
}

#[repr(C, packed)]
#[derive(Copy, VClone)]
pub struct SetupHeader {
    pub setup_sects: u8,
    pub root_flags: u16,
    pub syssize: u32,
    pub ram_size: u16,
    pub vid_mode: u16,
    pub root_dev: u16,
    pub boot_flag: u16,
    pub jump: u16,
    pub header: u32,
    pub version: u16,
    pub realmode_swtch: u32,
    pub start_sys_seg: u16,
    pub kernel_version: u16,
    pub type_of_loader: u8,
    pub loadflags: u8,
    pub setup_move_size: u16,
    pub code32_start: u32,
    pub ramdisk_image: u32,
    pub ramdisk_size: u32,
    pub bootsect_kludge: u32,
    pub heap_end_ptr: u16,
    pub ext_loader_ver: u8,
    pub ext_loader_type: u8,
    pub cmd_line_ptr: u32,
    pub initrd_addr_max: u32,
    pub kernel_alignment: u32,
    pub relocatable_kernel: u8,
    pub min_alignment: u8,
    pub xloadflags: u16,
    pub cmdline_size: u32,
    pub hardware_subarch: u32,
    pub hardware_subarch_data: u64,
    pub payload_offset: u32,
    pub payload_length: u32,
    pub setup_data: u64,
    pub pref_address: u64,
    pub init_size: u32,
    pub handover_offset: u32,
    pub kernel_info_offset: u32,
}

// NOTE: Rust warns that 1. align(1) structure needs Copy, 2. Copy needs Clone;
#[repr(C, packed)]
#[derive(SpecGetter, SpecSetter, Copy, VClone)]
pub struct BootParams {
    pub _pad0: [u8; 0x70],
    pub acpi_rsdp_addr: u64, // 0x070
    pub _pad1: [u8; 0x50],
    pub _ext_cmd_line_ptr: u32, // 0xc8
    pub _pad2_0: Array<u8, { 0x13c - 0xc8 - 4 }>,
    pub cc_blob_addr: u32, // 0x13c
    pub _pad2_1: Array<u8, { 0x1e8 - 0x13c - 4 }>,
    #[def_offset]
    pub e820_entries: u8, // 0x1e8
    pub reserved_4: Array<u8, { 0x1f1 - 0x1e8 - 1 }>,
    pub hdr: SetupHeader, // 0x1f1
    pub reserved_5: Array<u8, { 0x2d0 - 0x1f1 - 123 }>,
    #[def_offset]
    pub e820: E820Table, // 0x2d0
    pub reserved_6: Array<u8, { 4096 - 0xcd0 }>,
}
}
