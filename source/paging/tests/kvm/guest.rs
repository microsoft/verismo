#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;
use core::sync::atomic::{AtomicU64, Ordering};

use paging::{
    address::{Address, PhysAddr, VirtAddr},
    arch::x86_64::{
        Cr3, Cr3Value, Cr4, Cr4Value, FlushScope, PTEntryFlags, X86_64Paging, X86_64PagingParams,
    },
    pagetable::{ActivePageTable, KernelPageTable},
    structs::{
        AllRootEntries, DirectMappedAllocator, Huge, KernelPolicy, Lvl, Page, PageSize,
        PagingError, PhysFrame, Regular,
    },
};

const ALIAS_ADDRESS: usize = 0x4000_0000;
const DIRECT_MAP_BASE: usize = 0xffff_8000_0000_0000;
const SERIAL_PORT: u16 = 0x3f8;
const DEBUG_EXIT_PORT: u16 = 0xf4;
const TABLE_PAGE_COUNT: usize = 64;
const TEST_VALUE: u64 = 0x5645_5249_4f53_5054;
const BOOTSTRAP_MAGIC: [u64; 8] = [
    0x4253_5452_4150_0001,
    0x4253_5452_4150_0002,
    0x4253_5452_4150_0003,
    0x4253_5452_4150_0004,
    0x4253_5452_4150_0005,
    0x4253_5452_4150_0006,
    0x4253_5452_4150_0007,
    0x4253_5452_4150_0008,
];
const TLB_FLUSH_ALL_THRESHOLD: usize = 256;
const CR4_PGE: usize = 1 << 7;
const EXPECTED_BOOT_SIGNATURE: [u8; 16] = *b"VERIOS-PT-IMAGE!";

global_asm!(include_str!("entry.S"), options(att_syntax));

extern "C" {
    static __boot_image_load_start: u8;
    static __boot_image_load_end: u8;
    static __boot_image_content_start: u8;
    static __boot_image_content_end: u8;
}

#[used]
#[link_section = ".rodata.boot_signature"]
static BOOT_IMAGE_SIGNATURE: [u8; 16] = EXPECTED_BOOT_SIGNATURE;

#[derive(Clone, Copy)]
#[repr(C, align(4096))]
struct AlignedPage([u8; 4096]);

#[repr(C)]
struct DirectMapArena {
    tables: [AlignedPage; TABLE_PAGE_COUNT],
    probe: AlignedPage,
    switch_probe: AlignedPage,
}

static mut DIRECT_MAP_ARENA: DirectMapArena = DirectMapArena {
    tables: [AlignedPage([0; 4096]); TABLE_PAGE_COUNT],
    probe: AlignedPage([0; 4096]),
    switch_probe: AlignedPage([0; 4096]),
};
static ALLOCATED_TABLES: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GuestPaging;

unsafe impl X86_64PagingParams for GuestPaging {
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
        let physical_start = core::ptr::addr_of!(__boot_image_load_start) as usize;
        let physical_end = core::ptr::addr_of!(__boot_image_load_end) as usize;
        (
            PhysAddr::from(physical_start)..PhysAddr::from(physical_end),
            VirtAddr::from(DIRECT_MAP_BASE + physical_start),
        )
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
                    let base = core::ptr::addr_of_mut!(DIRECT_MAP_ARENA).cast::<AlignedPage>();
                    return Ok(PhysAddr::from(unsafe { base.add(index) } as usize));
                }
                Err(observed) => allocated = observed,
            }
        }
    }

    unsafe fn deallocate_table_page(paddr: PhysAddr) {
        let base = core::ptr::addr_of_mut!(DIRECT_MAP_ARENA).cast::<AlignedPage>() as usize;
        let index = (paddr.bits() - base) / 4096;
        ALLOCATED_TABLES.fetch_and(!(1 << index), Ordering::AcqRel);
    }
}

type Arch = X86_64Paging<GuestPaging>;

type GuestPageTable = KernelPageTable<Arch, GuestAllocator, Lvl<3>>;
type ActiveGuestPageTable =
    ActivePageTable<Arch, GuestAllocator, Lvl<3>, KernelPolicy<AllRootEntries>>;

fn build_table() -> GuestPageTable {
    let table = match GuestPageTable::new(PTEntryFlags::data()) {
        Ok(table) => table,
        Err(_) => fail("VERIOS_PAGETABLE_BUILD_FAILED\n"),
    };

    // The built-in locks in BSS must remain accessible after loading this root.
    let image_end = core::ptr::addr_of!(__boot_image_load_end) as usize;
    let identity_end = (image_end + Huge::SIZE - 1) & !(Huge::SIZE - 1);
    for address in (0..identity_end).step_by(Huge::SIZE) {
        let page = Page::<Huge>::from_start_address(VirtAddr::from(address))
            .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_IDENTITY_PAGE_INVALID\n"));
        let frame = PhysFrame::<Huge>::from_start_address(PhysAddr::from(address))
            .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_IDENTITY_FRAME_INVALID\n"));
        if table
            .map(
                page,
                frame,
                PTEntryFlags::PRESENT
                    | PTEntryFlags::WRITABLE
                    | PTEntryFlags::ACCESSED
                    | PTEntryFlags::DIRTY,
                false,
            )
            .is_err()
        {
            fail("VERIOS_PAGETABLE_IDENTITY_MAP_FAILED\n");
        }
    }
    table
}

/// Builds, activates, and exercises a page table created by the paging crate.
#[no_mangle]
pub extern "C" fn kmain() -> ! {
    serial_init();
    serial_write("VERIOS_PAGETABLE_BOOT_START\n");

    let arena = core::ptr::addr_of_mut!(DIRECT_MAP_ARENA).cast::<AlignedPage>();
    let test_paddr = unsafe { arena.add(TABLE_PAGE_COUNT) } as usize;
    let bootstrap_probe = test_paddr as *mut u64;
    for (index, value) in BOOTSTRAP_MAGIC.iter().enumerate() {
        unsafe { bootstrap_probe.add(index).write_volatile(*value) };
    }
    serial_write("VERIOS_PAGETABLE_BOOTSTRAP_MAGIC_WRITTEN\n");

    let table = build_table();
    serial_write("VERIOS_PAGETABLE_BUILD_OK\n");

    let direct_map_vaddr = GuestAllocator::resolve_paddr(PhysAddr::from(test_paddr));
    if table.phys_addr(direct_map_vaddr) != Ok(PhysAddr::from(test_paddr)) {
        fail("VERIOS_PAGETABLE_DIRECT_MAP_WALK_FAILED\n");
    }

    let page = Page::<Regular>::from_start_address(VirtAddr::from(ALIAS_ADDRESS))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_ALIAS_INVALID\n"));
    let frame = PhysFrame::<Regular>::from_start_address(PhysAddr::from(test_paddr))
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

    let root = table.leak();
    Cr3.write(Cr3Value::from_bits_retain(root.bits() as u64));
    // SAFETY: this BSP remains on one CPU, and the new root maps its image,
    // stacks and allocator. The bootstrap root and all translations remain valid.
    let table = unsafe { ActiveGuestPageTable::from_current_cpu() }
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_CURRENT_ROOT_FAILED\n"));
    serial_write("VERIOS_PAGETABLE_CR3_OK\n");

    let alias = ALIAS_ADDRESS as *mut u64;
    let direct_map_probe = direct_map_vaddr.as_mut_ptr::<u64>();
    for (index, expected) in BOOTSTRAP_MAGIC.iter().enumerate() {
        if unsafe { direct_map_probe.add(index).read_volatile() } != *expected {
            fail("VERIOS_PAGETABLE_BOOTSTRAP_MAGIC_FAILED\n");
        }
    }
    serial_write("VERIOS_PAGETABLE_BOOTSTRAP_MAGIC_OK\n");

    unsafe {
        alias.write_volatile(TEST_VALUE);
        if direct_map_probe.read_volatile() != TEST_VALUE {
            fail("VERIOS_PAGETABLE_DIRECT_MAP_HARDWARE_FAILED\n");
        }
    }
    serial_write("VERIOS_PAGETABLE_DIRECT_MAP_OK\n");
    let original_cr3 = Cr3.read();
    if original_cr3.bits() as usize != root.bits() {
        fail("VERIOS_PAGETABLE_CR3_FAILED\n");
    }
    // Both bits are valid as PWT/PCD or PCID bits; writes flush retained entries.
    let changed_cr3 = original_cr3 ^ (Cr3Value::PWT | Cr3Value::PCD);
    Cr3.write(changed_cr3);
    let observed_cr3 = Cr3.read();
    Cr3.write(original_cr3);
    if observed_cr3 != changed_cr3 || Cr3.read() != original_cr3 {
        fail("VERIOS_PAGETABLE_CR3_READ_WRITE_FAILED\n");
    }
    serial_write("VERIOS_PAGETABLE_CR3_READ_WRITE_OK\n");
    verify_boot_image();
    let table = verify_switch_to(table);

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

fn verify_switch_to(table: ActiveGuestPageTable) -> ActiveGuestPageTable {
    let original_root = table.root_paddr();
    let original_allocations = ALLOCATED_TABLES.load(Ordering::Acquire);
    let next = build_table();
    let next_root = next.root_paddr();
    let probe = unsafe { core::ptr::addr_of_mut!(DIRECT_MAP_ARENA.switch_probe).cast::<u64>() };
    unsafe { probe.write_volatile(!TEST_VALUE) };
    let page = Page::<Regular>::from_start_address(VirtAddr::from(ALIAS_ADDRESS))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SWITCH_ALIAS_INVALID\n"));
    let frame = PhysFrame::<Regular>::from_start_address(PhysAddr::from(probe as usize))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SWITCH_FRAME_INVALID\n"));
    next.map(page, frame, PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::NX, false)
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SWITCH_MAP_FAILED\n"));
    let before_switch = ALLOCATED_TABLES.load(Ordering::Acquire);
    let flags = (Cr3Value::PWT | Cr3Value::PCD).bits() as usize;
    // SAFETY: this BSP alone uses these roots; both map its image, stack and allocator.
    let (table, retired) = unsafe { table.switch_to(next, flags) }
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SWITCH_FAILED\n"));
    let alias = ALIAS_ADDRESS as *const u64;
    if next_root == original_root
        || Cr3.read().bits() as usize != (next_root.bits() | flags)
        || retired.root_paddr() != original_root
        || ALLOCATED_TABLES.load(Ordering::Acquire) != before_switch
        || unsafe { alias.read_volatile() } != !TEST_VALUE
    {
        fail("VERIOS_PAGETABLE_SWITCH_HARDWARE_FAILED\n");
    }
    let adopted_root = table.leak();
    // SAFETY: the leaked binding transfers this CPU's current tree exactly once.
    let table = unsafe { ActiveGuestPageTable::from_current_cpu() }
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_CURRENT_ROOT_FAILED\n"));
    if table.root_paddr() != adopted_root
        || Cr3.read().bits() as usize != (next_root.bits() | flags)
        || ALLOCATED_TABLES.load(Ordering::Acquire) != before_switch
    {
        fail("VERIOS_PAGETABLE_CURRENT_ROOT_CHANGED\n");
    }
    serial_write("VERIOS_PAGETABLE_CURRENT_ROOT_OK\n");
    flush_tlb_all(true);
    // SAFETY: the single CPU switched away and flushed all retained translations.
    let original = unsafe { retired.into_page_table() };
    // SAFETY: the original root still maps all required execution and allocator state.
    let (table, retired) = unsafe { table.switch_to(original, 0) }
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SWITCH_BACK_FAILED\n"));
    if Cr3.read().bits() as usize != original_root.bits()
        || retired.root_paddr() != next_root
        || unsafe { alias.read_volatile() } != TEST_VALUE
    {
        fail("VERIOS_PAGETABLE_SWITCH_BACK_HARDWARE_FAILED\n");
    }
    flush_tlb_all(true);
    // SAFETY: no other CPU uses the retired root, and all translations were flushed.
    drop(unsafe { retired.into_page_table() });
    if ALLOCATED_TABLES.load(Ordering::Acquire) != original_allocations {
        fail("VERIOS_PAGETABLE_SWITCH_RECLAIM_FAILED\n");
    }
    serial_write("VERIOS_PAGETABLE_SWITCH_TO_OK\n");
    table
}

/// Compares immutable boot-image bytes with their high direct-map aliases.
fn verify_boot_image() {
    let content_start = core::ptr::addr_of!(__boot_image_content_start) as usize;
    let content_end = core::ptr::addr_of!(__boot_image_content_end) as usize;
    let direct_content =
        GuestAllocator::resolve_paddr(PhysAddr::from(content_start)).as_ptr::<u8>();
    let identity_hash = image_checksum(content_start as *const u8, content_end - content_start);
    let direct_hash = image_checksum(direct_content, content_end - content_start);
    if identity_hash != direct_hash {
        fail("VERIOS_PAGETABLE_BOOT_IMAGE_HASH_FAILED\n");
    }

    let signature_paddr = core::ptr::addr_of!(BOOT_IMAGE_SIGNATURE) as usize;
    let direct_signature =
        GuestAllocator::resolve_paddr(PhysAddr::from(signature_paddr)).as_ptr::<u8>();
    for (index, expected) in EXPECTED_BOOT_SIGNATURE.iter().enumerate() {
        if unsafe { direct_signature.add(index).read_volatile() } != *expected {
            fail("VERIOS_PAGETABLE_BOOT_IMAGE_CONTENT_FAILED\n");
        }
    }
    serial_write("VERIOS_PAGETABLE_BOOT_IMAGE_OK\n");
}

/// Hashes image bytes with volatile reads so both virtual paths reach memory.
fn image_checksum(start: *const u8, len: usize) -> u64 {
    let mut hash = 0xcbf2_9ce4_8422_2325u64;
    for index in 0..len {
        hash ^= unsafe { start.add(index).read_volatile() } as u64;
        hash = hash.wrapping_mul(0x100_0000_01b3);
    }
    hash
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
    let cr4 = Cr4.read();
    Cr4.write(cr4 ^ Cr4Value::from_bits_retain(CR4_PGE as u64));
    Cr4.write(cr4);
}

/// Reloads the active root to invalidate local translations.
fn reload_cr3() {
    Cr3.write(Cr3.read());
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
