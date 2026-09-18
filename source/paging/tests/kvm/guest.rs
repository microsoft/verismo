#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;
use core::sync::atomic::{AtomicU64, Ordering};

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::frame::PhysFrame;
use paging::level::Lvl;
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::page::Page;
use paging::pagetable::PageTable;
use paging::sizes::Size4KiB;
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

const ALIAS_ADDRESS: usize = 0x4000_0000;
const IDENTITY_MAP_END: usize = ALIAS_ADDRESS;
const SERIAL_PORT: u16 = 0x3f8;
const DEBUG_EXIT_PORT: u16 = 0xf4;
const TABLE_PAGE_COUNT: usize = 64;
const TEST_VALUE: u64 = 0x5645_5249_4f53_5054;
const TLB_FLUSH_ALL_THRESHOLD: usize = 256;
const CR4_PGE: usize = 1 << 7;

global_asm!(include_str!("entry.S"), options(att_syntax));

#[derive(Clone, Copy)]
#[repr(C, align(4096))]
struct AlignedPage([u8; 4096]);

static mut TABLE_ARENA: [AlignedPage; TABLE_PAGE_COUNT] =
    [AlignedPage([0; 4096]); TABLE_PAGE_COUNT];
static ALLOCATED_TABLES: AtomicU64 = AtomicU64::new(0);
static mut TEST_PAGE: AlignedPage = AlignedPage([0; 4096]);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GuestPaging;

unsafe impl X86PagingParams for GuestPaging {
    fn private_mask() -> usize {
        0
    }

    fn supported_flags() -> PTEntryFlags {
        PTEntryFlags::all()
    }

    fn flush_tlb_global_sync(scope: FlushScope) {
        flush_tlb_scope(scope, true);
    }

    fn flush_tlb_global_percpu(scope: FlushScope) {
        flush_tlb_scope(scope, true);
    }

    fn flush_tlb_ignore_global_sync(scope: FlushScope) {
        flush_tlb_scope(scope, false);
    }
}

struct GuestAllocator;

unsafe impl DirectMappedAllocator for GuestAllocator {
    fn direct_map() -> (core::ops::Range<PhysAddr>, VirtAddr) {
        (PhysAddr::from(0usize)..PhysAddr::from(IDENTITY_MAP_END), VirtAddr::from(0usize))
    }

    fn allocate_table_page() -> Result<PhysAddr, PagingError> {
        let mut allocated = ALLOCATED_TABLES.load(Ordering::Relaxed);
        loop {
            let index = (!allocated).trailing_zeros() as usize;
            if index >= TABLE_PAGE_COUNT {
                return Err(PagingError::AllocFrame);
            }
            let next = allocated | (1 << index);
            match ALLOCATED_TABLES.compare_exchange_weak(
                allocated,
                next,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    let base = core::ptr::addr_of_mut!(TABLE_ARENA).cast::<AlignedPage>();
                    return Ok(PhysAddr::from(unsafe { base.add(index) } as usize));
                }
                Err(observed) => allocated = observed,
            }
        }
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        let base = core::ptr::addr_of_mut!(TABLE_ARENA).cast::<AlignedPage>() as usize;
        let index = (paddr.bits() - base) / 4096;
        ALLOCATED_TABLES.fetch_and(!(1 << index), Ordering::AcqRel);
    }
}

type Arch = X86Paging<GuestPaging>;
type GuestPageTable = PageTable<Arch, GuestAllocator, Lvl<3>>;

/// Builds, activates, and exercises a page table created by the paging crate.
#[no_mangle]
pub extern "C" fn kmain() -> ! {
    serial_init();
    serial_write("VERIOS_PAGETABLE_BOOT_START\n");

    let mut table = match GuestPageTable::new(
        PTEntryFlags::PRESENT
            | PTEntryFlags::WRITABLE
            | PTEntryFlags::ACCESSED
            | PTEntryFlags::DIRTY,
    ) {
        Ok(table) => table,
        Err(_) => fail("VERIOS_PAGETABLE_BUILD_FAILED\n"),
    };
    serial_write("VERIOS_PAGETABLE_BUILD_OK\n");

    let test_paddr = core::ptr::addr_of_mut!(TEST_PAGE) as usize;
    let page = Page::<Size4KiB>::from_start_address(VirtAddr::from(ALIAS_ADDRESS))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_ALIAS_INVALID\n"));
    let frame = PhysFrame::<Size4KiB>::from_start_address(PhysAddr::from(test_paddr))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_FRAME_INVALID\n"));
    let initial_alias_flags = PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::NX
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY;
    if table.map(page, frame, initial_alias_flags, false).is_err() {
        fail("VERIOS_PAGETABLE_MAP_FAILED\n");
    }
    if table.validate_page_table().is_err()
        || table.phys_addr(VirtAddr::from(ALIAS_ADDRESS)) != Ok(PhysAddr::from(test_paddr))
    {
        fail("VERIOS_PAGETABLE_WALK_FAILED\n");
    }
    serial_write("VERIOS_PAGETABLE_MAP_OK\n");

    let root = table.root_paddr();
    load_cr3(root.bits());
    serial_write("VERIOS_PAGETABLE_CR3_OK\n");

    let alias = ALIAS_ADDRESS as *mut u64;
    let backing = core::ptr::addr_of_mut!(TEST_PAGE).cast::<u64>();
    unsafe {
        alias.write_volatile(TEST_VALUE);
        if backing.read_volatile() != TEST_VALUE {
            fail("VERIOS_PAGETABLE_HARDWARE_WALK_FAILED\n");
        }
    }
    if read_cr3() != root.bits() {
        fail("VERIOS_PAGETABLE_CR3_FAILED\n");
    }

    let nonglobal_flags = PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE;
    match table.set_flags(page, nonglobal_flags, true) {
        Ok(flush) => flush.flush_tlb_ignore_global_sync(),
        Err(_) => fail("VERIOS_PAGETABLE_SYNC_FLUSH_FAILED\n"),
    }
    match table.set_flags(page, PTEntryFlags::data(), false) {
        Ok(flush) => flush.flush_tlb_global_percpu(),
        Err(_) => fail("VERIOS_PAGETABLE_PERCPU_FLUSH_FAILED\n"),
    }

    let leaked_root = table.leak();
    if leaked_root != root {
        fail("VERIOS_PAGETABLE_ROOT_CHANGED\n");
    }
    serial_write("VERIOS_PAGETABLE_BOOT_OK\n");
    unsafe { outb(DEBUG_EXIT_PORT, 0x10) };
    halt()
}

/// Flushes a range or widens a large request to a complete local invalidation.
fn flush_tlb_scope(scope: FlushScope, include_global: bool) {
    let FlushScope::Range { start, end, level } = scope else {
        flush_tlb_all(include_global);
        return;
    };
    let page_size = level.size();
    let page_count = (end.bits() - start.bits()).div_ceil(page_size);
    if page_count > TLB_FLUSH_ALL_THRESHOLD {
        flush_tlb_all(include_global);
        return;
    }
    let mut address = start.bits();
    while address < end.bits() {
        invalidate_page(address);
        address += page_size;
    }
}

/// Flushes all local translations, optionally including global entries.
fn flush_tlb_all(include_global: bool) {
    if !include_global {
        reload_cr3();
        return;
    }
    let cr4 = read_cr4();
    write_cr4(cr4 ^ CR4_PGE);
    write_cr4(cr4);
}

/// Reloads the active root to invalidate local translations.
fn reload_cr3() {
    let root = read_cr3();
    load_cr3(root);
}

/// Installs the supplied physical root in CR3.
fn load_cr3(root: usize) {
    unsafe {
        asm!("mov cr3, {}", in(reg) root, options(nostack, preserves_flags));
    }
}

/// Reads the currently active physical page-table root.
fn read_cr3() -> usize {
    let root;
    unsafe {
        asm!("mov {}, cr3", out(reg) root, options(nostack, preserves_flags));
    }
    root
}

/// Reads the current CR4 control flags.
fn read_cr4() -> usize {
    let cr4;
    unsafe {
        asm!("mov {}, cr4", out(reg) cr4, options(nostack, preserves_flags));
    }
    cr4
}

/// Writes CR4 while preserving every flag not selected by the caller.
fn write_cr4(cr4: usize) {
    unsafe {
        asm!("mov cr4, {}", in(reg) cr4, options(nostack, preserves_flags));
    }
}

/// Invalidates the local translation containing `address`.
fn invalidate_page(address: usize) {
    unsafe {
        asm!("invlpg [{}]", in(reg) address, options(nostack, preserves_flags));
    }
}

/// Initializes the first 16550-compatible serial port.
fn serial_init() {
    unsafe {
        outb(SERIAL_PORT + 1, 0x00);
        outb(SERIAL_PORT + 3, 0x80);
        outb(SERIAL_PORT, 0x03);
        outb(SERIAL_PORT + 1, 0x00);
        outb(SERIAL_PORT + 3, 0x03);
        outb(SERIAL_PORT + 2, 0xc7);
        outb(SERIAL_PORT + 4, 0x0b);
    }
}

/// Writes one byte after the UART accepts another transmit character.
fn serial_write_byte(byte: u8) {
    while unsafe { inb(SERIAL_PORT + 5) } & 0x20 == 0 {
        core::hint::spin_loop();
    }
    unsafe { outb(SERIAL_PORT, byte) };
}

/// Writes an ASCII status marker to the serial console.
fn serial_write(message: &str) {
    for byte in message.bytes() {
        serial_write_byte(byte);
    }
}

/// Reports a deterministic failure marker before stopping the guest.
fn fail(message: &str) -> ! {
    serial_write(message);
    unsafe { outb(DEBUG_EXIT_PORT, 0x11) };
    halt()
}

/// Stops execution when the VMM does not implement the debug-exit port.
fn halt() -> ! {
    loop {
        unsafe { asm!("cli; hlt", options(nomem, nostack)) };
    }
}

/// Writes one byte to an x86 I/O port.
unsafe fn outb(port: u16, value: u8) {
    unsafe {
        asm!("out dx, al", in("dx") port, in("al") value, options(nomem, nostack, preserves_flags));
    }
}

/// Reads one byte from an x86 I/O port.
unsafe fn inb(port: u16) -> u8 {
    let value;
    unsafe {
        asm!("in al, dx", in("dx") port, out("al") value, options(nomem, nostack, preserves_flags));
    }
    value
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    serial_init();
    fail("VERIOS_PAGETABLE_PANIC\n")
}
