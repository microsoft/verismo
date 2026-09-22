//! Four-CPU x86_64 Xen PVH boot test for the `concurrent` `PageTable`. The BSP
//! constructs one shared table and starts three APs, which then race with the
//! BSP mapping and unmapping their own 4 KiB pages within a shared 2 MiB
//! region, exercising concurrent structural growth and entry updates.
#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};
use core::panic::PanicInfo;
use core::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, AtomicUsize, Ordering};

use paging::address::{Address, PhysAddr, VirtAddr};
use paging::frame::PhysFrame;
use paging::level::{Lvl, PageLevel};
use paging::os_contract::{DirectMappedAllocator, PagingError};
use paging::page::Page;
use paging::pagetable::{LockSpec, PageTable};
use paging::sizes::{PageSize, Regular};
use paging::{FlushScope, PTEntryFlags, X86Paging, X86PagingParams};

const SERIAL_PORT: u16 = 0x3f8;
const DEBUG_EXIT_PORT: u16 = 0xf4;
const TLB_FLUSH_ALL_THRESHOLD: usize = 256;
const CR4_PGE: usize = 1 << 7;

const AP_COUNT: usize = 3;
const NUM_WORKERS: usize = AP_COUNT + 1;
const STACK_SIZE: usize = 16 * 1024;
const TABLE_PAGE_COUNT: usize = 16;
const ROUNDS: usize = 512;
const WORKLOAD_BASE_VA: usize = 0x4000_0000;

const APIC_BASE_MSR: u32 = 0x1b;
const X2APIC_ICR_MSR: u32 = 0x830;
const X2APIC_ENABLE_BITS: u64 = (1 << 10) | (1 << 11);
const APIC_MMIO_ICR_LOW_OFFSET: usize = 0x300;
const APIC_MMIO_ICR_HIGH_OFFSET: usize = 0x310;
const APIC_MMIO_DELIVERY_STATUS_BIT: u32 = 1 << 12;
const ICR_DELIVERY_INIT: u32 = 0x0000_4500;
const ICR_DELIVERY_INIT_DEASSERT: u32 = 0x0000_8500;
const ICR_DELIVERY_STARTUP: u32 = 0x0000_4600;
const IPI_STEP_DELAY_ITERATIONS: usize = 200_000;
const SIPI_RETRY_WAIT_ITERATIONS: usize = 2_000_000;
const BOUNDED_SPIN_ITERATIONS: usize = 20_000_000;

global_asm!(include_str!("entry-smp.S"), options(att_syntax));

extern "C" {
    static ap_trampoline_start: u8;
    static ap_trampoline_end: u8;
    static __boot_image_load_end: u8;
}

/// The fixed low physical scratch address the AP trampoline is copied to
/// and executed from; matches `entry-smp.S`'s `TRAMPOLINE_BASE`. The SIPI
/// vector is this divided by 4 KiB.
const TRAMPOLINE_BASE: usize = 0x8000;

/// Published once by the BSP before the first SIPI; read directly by the
/// 32-bit trampoline (`entry-smp.S`), so its layout must stay a plain `u64`.
#[no_mangle]
static AP_ROOT_PA: AtomicU64 = AtomicU64::new(0);
/// Published by the BSP for one AP before its SIPI; read by the 64-bit
/// trampoline to set that AP's initial stack pointer.
#[no_mangle]
static AP_STACK_TOP: AtomicU64 = AtomicU64::new(0);
/// Published by the BSP for one AP before its SIPI; read by the 64-bit
/// trampoline and passed to [`ap_main`] as its first argument.
#[no_mangle]
static AP_WORKER_ID: AtomicU64 = AtomicU64::new(0);

/// Set by an AP once it has entered Rust; the BSP waits on this before
/// starting the next AP so trampoline state is never shared concurrently.
static AP_READY: AtomicBool = AtomicBool::new(false);
static WORKLOAD_START: AtomicBool = AtomicBool::new(false);
static COMPLETED_WORKERS: AtomicUsize = AtomicUsize::new(0);
static WORKLOAD_FAILED: AtomicBool = AtomicBool::new(false);

/// Whether IPIs go through the x2APIC MSR interface or the legacy
/// MMIO-mapped local APIC; set once by [`configure_apic`] before any AP starts.
static USE_X2APIC: AtomicBool = AtomicBool::new(false);
/// The legacy local APIC's identity-mapped MMIO base, valid only when
/// `USE_X2APIC` is false.
static APIC_MMIO_BASE: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Copy)]
#[repr(C, align(4096))]
struct AlignedPage([u8; 4096]);

#[repr(C, align(16))]
struct ApStack([u8; STACK_SIZE]);

static mut AP_STACKS: [ApStack; AP_COUNT] =
    [ApStack([0; STACK_SIZE]), ApStack([0; STACK_SIZE]), ApStack([0; STACK_SIZE])];
static mut WORKER_FRAMES: [AlignedPage; NUM_WORKERS] = [AlignedPage([0; 4096]); NUM_WORKERS];

#[repr(C)]
struct TableArena {
    tables: [AlignedPage; TABLE_PAGE_COUNT],
}

static mut TABLE_ARENA: TableArena =
    TableArena { tables: [AlignedPage([0; 4096]); TABLE_PAGE_COUNT] };
static ALLOCATED_TABLES: AtomicU64 = AtomicU64::new(0);

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

/// Table-page allocator whose direct map is the identity function: every
/// table page lives inside `TABLE_ARENA`, itself inside the identity-mapped
/// low range, so physical and virtual addresses coincide.
struct GuestAllocator;

unsafe impl DirectMappedAllocator for GuestAllocator {
    fn direct_map() -> (core::ops::Range<PhysAddr>, VirtAddr) {
        let image_end = core::ptr::addr_of!(__boot_image_load_end) as usize;
        let mapped_end = (image_end + Regular::SIZE - 1) & !(Regular::SIZE - 1);
        (PhysAddr::from(0usize)..PhysAddr::from(mapped_end), VirtAddr::from(0usize))
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

/// One striped spin-lock cell keyed by a table page's physical address.
struct SpinLockCell {
    locked: AtomicBool,
    cell: UnsafeCell<()>,
}

impl SpinLockCell {
    const fn new() -> Self {
        Self { locked: AtomicBool::new(false), cell: UnsafeCell::new(()) }
    }
}

// SAFETY: `cell` holds no data of its own (`T = ()`); every access is guarded
// by the CAS on `locked`, which excludes every other guard for this stripe.
unsafe impl Sync for SpinLockCell {}

const LOCK_STRIPES: usize = 8;

/// A minimal striped spin mutex satisfying `LockSpec<()>` for the concurrent
/// `PageTable`. Stripe selection is keyed by physical page number, so every
/// key maps to a stable stripe across the whole tree's lifetime.
struct SpinStripes {
    stripes: [SpinLockCell; LOCK_STRIPES],
}

impl SpinStripes {
    const fn new() -> Self {
        Self {
            stripes: [
                SpinLockCell::new(),
                SpinLockCell::new(),
                SpinLockCell::new(),
                SpinLockCell::new(),
                SpinLockCell::new(),
                SpinLockCell::new(),
                SpinLockCell::new(),
                SpinLockCell::new(),
            ],
        }
    }
}

struct SpinGuard<'a> {
    locked: &'a AtomicBool,
    cell: &'a UnsafeCell<()>,
}

impl Deref for SpinGuard<'_> {
    type Target = ();

    fn deref(&self) -> &() {
        unsafe { &*self.cell.get() }
    }
}

impl DerefMut for SpinGuard<'_> {
    fn deref_mut(&mut self) -> &mut () {
        unsafe { &mut *self.cell.get() }
    }
}

impl Drop for SpinGuard<'_> {
    fn drop(&mut self) {
        self.locked.store(false, Ordering::Release);
    }
}

// SAFETY: a stable physical key always selects the same stripe. The CAS
// acquire/release pair excludes every other guard for that stripe, and
// dropping the guard always releases it without panicking.
unsafe impl LockSpec<()> for SpinStripes {
    type Guard<'a> = SpinGuard<'a>;

    fn lock(&self, page: PhysAddr) -> Self::Guard<'_> {
        let stripe = (page.bits() >> 12) % LOCK_STRIPES;
        let locked = &self.stripes[stripe].locked;
        while locked
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            core::hint::spin_loop();
        }
        SpinGuard { locked, cell: &self.stripes[stripe].cell }
    }
}

type Arch = X86Paging<GuestPaging>;
type SmpTable = PageTable<Arch, GuestAllocator, Lvl<3>, SpinStripes>;

const _: fn() = || {
    fn assert_sync<T: Sync>() {}
    assert_sync::<SmpTable>();
};

static TABLE_PTR: AtomicPtr<SmpTable> = AtomicPtr::new(core::ptr::null_mut());
static mut TABLE_STORAGE: MaybeUninit<SmpTable> = MaybeUninit::uninit();

/// Spins until `condition` holds or the bounded iteration budget runs out.
/// Every wait in this guest is bounded except lock CAS loops, which external
/// concurrency prevents from having a static bound.
fn spin_wait(mut condition: impl FnMut() -> bool, timeout_marker: &str) {
    for _ in 0..BOUNDED_SPIN_ITERATIONS {
        if condition() {
            return;
        }
        core::hint::spin_loop();
    }
    fail(timeout_marker);
}

fn spin_delay(iterations: usize) {
    for _ in 0..iterations {
        core::hint::spin_loop();
    }
}

/// Reads a model-specific register.
unsafe fn rdmsr(msr: u32) -> u64 {
    let (low, high): (u32, u32);
    unsafe {
        asm!("rdmsr", in("ecx") msr, out("eax") low, out("edx") high, options(nostack, preserves_flags));
    }
    ((high as u64) << 32) | low as u64
}

/// Writes a model-specific register.
unsafe fn wrmsr(msr: u32, value: u64) {
    let low = value as u32;
    let high = (value >> 32) as u32;
    unsafe {
        asm!("wrmsr", in("ecx") msr, in("eax") low, in("edx") high, options(nostack, preserves_flags));
    }
}

/// Enables x2APIC mode (bits 10 and 11 of `IA32_APIC_BASE`) so the ICR can be
/// sent as one 64-bit MSR write, and confirms it stuck by reading the MSR
/// back: some QEMU/TCG releases predate x2APIC MSR support and silently
/// ignore this write. When that happens, this maps the legacy MMIO-mapped
/// local APIC's page (every QEMU version and all real hardware implement
/// it) into `table` instead.
fn configure_apic(table: &SmpTable) {
    let base_msr = unsafe { rdmsr(APIC_BASE_MSR) };
    unsafe { wrmsr(APIC_BASE_MSR, base_msr | X2APIC_ENABLE_BITS) };
    if unsafe { rdmsr(APIC_BASE_MSR) } & X2APIC_ENABLE_BITS == X2APIC_ENABLE_BITS {
        USE_X2APIC.store(true, Ordering::Relaxed);
        serial_write("VERIOS_PAGETABLE_SMP_APIC_MODE_X2\n");
        return;
    }

    let mmio_base = base_msr as usize & 0xffff_f000;
    let page = Page::<Regular>::from_start_address(VirtAddr::from(mmio_base))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SMP_APIC_MMIO_VA_INVALID\n"));
    let frame = PhysFrame::<Regular>::from_start_address(PhysAddr::from(mmio_base))
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SMP_APIC_MMIO_FRAME_INVALID\n"));
    let flags =
        PTEntryFlags::PRESENT | PTEntryFlags::WRITABLE | PTEntryFlags::NX | PTEntryFlags::NO_CACHE;
    if table.map(page, frame, flags, false).is_err() {
        fail("VERIOS_PAGETABLE_SMP_APIC_MMIO_MAP_FAILED\n");
    }
    APIC_MMIO_BASE.store(mmio_base, Ordering::Relaxed);
    serial_write("VERIOS_PAGETABLE_SMP_APIC_MODE_LEGACY\n");
}

/// Sends one interprocessor interrupt to `apic_id` through whichever local
/// APIC interface [`configure_apic`] selected.
fn send_icr(apic_id: u32, low: u32) {
    if USE_X2APIC.load(Ordering::Relaxed) {
        let icr = (u64::from(apic_id) << 32) | u64::from(low);
        unsafe { wrmsr(X2APIC_ICR_MSR, icr) };
        return;
    }
    let mmio_base = APIC_MMIO_BASE.load(Ordering::Relaxed);
    spin_wait(
        || unsafe { legacy_apic_read(mmio_base, APIC_MMIO_ICR_LOW_OFFSET) }
            & APIC_MMIO_DELIVERY_STATUS_BIT
            == 0,
        "VERIOS_PAGETABLE_SMP_APIC_BUSY_TIMEOUT\n",
    );
    unsafe {
        legacy_apic_write(mmio_base, APIC_MMIO_ICR_HIGH_OFFSET, apic_id << 24);
        legacy_apic_write(mmio_base, APIC_MMIO_ICR_LOW_OFFSET, low);
    }
}

/// # Safety
/// `mmio_base` must be the identity-mapped, currently valid local APIC MMIO
/// page, and `offset` must be a 4-byte-aligned register offset within it.
unsafe fn legacy_apic_read(mmio_base: usize, offset: usize) -> u32 {
    unsafe { (mmio_base as *const u32).byte_add(offset).read_volatile() }
}

/// # Safety
/// Same requirements as [`legacy_apic_read`].
unsafe fn legacy_apic_write(mmio_base: usize, offset: usize, value: u32) {
    unsafe { (mmio_base as *mut u32).byte_add(offset).write_volatile(value) };
}

/// Copies the AP trampoline from wherever the linker placed it (an
/// ordinary part of the main image) to the fixed low physical scratch
/// address SIPI requires. The trampoline's own code (`entry-smp.S`) computes
/// its internal addresses relative to `TRAMPOLINE_BASE`, not its link
/// address, so it runs correctly once copied here.
///
/// # Why not link the trampoline directly at the low address
/// QEMU's PVH direct-boot loader (used for this Xen-note ELF) miscopies
/// images whose PT_LOAD segments sit at addresses far apart: SeaBIOS loads
/// the raw kernel file as one flat block sized `elf_high - elf_low` at
/// `elf_low`, so a low segment reachable only through a huge address gap
/// does not reliably arrive with correct content.
fn install_trampoline() {
    let start = core::ptr::addr_of!(ap_trampoline_start);
    let end = core::ptr::addr_of!(ap_trampoline_end);
    let size = end as usize - start as usize;
    unsafe { core::ptr::copy_nonoverlapping(start, TRAMPOLINE_BASE as *mut u8, size) };
}

fn ap_stack_top(ap_index: usize) -> u64 {
    unsafe {
        let stack = core::ptr::addr_of!(AP_STACKS[ap_index - 1]);
        (stack as usize + STACK_SIZE) as u64
    }
}

/// Sends INIT/deassert/SIPI to `apic_id`, publishing that AP's stack and
/// worker id first, and waits for it to reach Rust before returning. A
/// second SIPI (the legacy MP-spec safety measure for pre-Pentium-4
/// processors) is sent only if the AP has not yet signaled ready: sending it
/// unconditionally risks re-delivering it while the first SIPI's trampoline
/// run is still in flight, forcing CS:IP back to the vector mid-transition.
/// APs are started one at a time so the trampoline's shared publication
/// state is never written for two APs at once.
fn start_ap(apic_id: u32) {
    AP_READY.store(false, Ordering::Relaxed);
    AP_STACK_TOP.store(ap_stack_top(apic_id as usize), Ordering::Release);
    AP_WORKER_ID.store(apic_id as u64, Ordering::Release);

    let startup_vector = (TRAMPOLINE_BASE / 0x1000) as u32;
    send_icr(apic_id, ICR_DELIVERY_INIT);
    spin_delay(IPI_STEP_DELAY_ITERATIONS);
    send_icr(apic_id, ICR_DELIVERY_INIT_DEASSERT);
    spin_delay(IPI_STEP_DELAY_ITERATIONS);
    send_icr(apic_id, ICR_DELIVERY_STARTUP | startup_vector);

    let mut became_ready = false;
    for _ in 0..SIPI_RETRY_WAIT_ITERATIONS {
        if AP_READY.load(Ordering::Acquire) {
            became_ready = true;
            break;
        }
        core::hint::spin_loop();
    }
    if !became_ready {
        send_icr(apic_id, ICR_DELIVERY_STARTUP | startup_vector);
    }

    spin_wait(|| AP_READY.load(Ordering::Acquire), "VERIOS_PAGETABLE_SMP_AP_STARTUP_TIMEOUT\n");
}

/// Maps, checks, and unmaps this worker's own 4 KiB page for `ROUNDS` bounded
/// rounds. Every worker's page lives in the same 2 MiB region, so the shared
/// intermediate tables down to the leaf level are built and contended for by
/// all four CPUs.
fn run_worker(table: &SmpTable, worker_id: usize) {
    let vaddr = VirtAddr::from(WORKLOAD_BASE_VA + worker_id * Regular::SIZE);
    let page = Page::<Regular>::from_start_address(vaddr)
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SMP_VA_INVALID\n"));
    let frame_paddr =
        PhysAddr::from(unsafe { core::ptr::addr_of!(WORKER_FRAMES[worker_id]) as usize });
    let frame = PhysFrame::<Regular>::from_start_address(frame_paddr)
        .unwrap_or_else(|_| fail("VERIOS_PAGETABLE_SMP_FRAME_INVALID\n"));
    let flags = PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::NX
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY;

    for _ in 0..ROUNDS {
        if table.map(page, frame, flags, false).is_err() {
            WORKLOAD_FAILED.store(true, Ordering::Release);
            break;
        }
        if table.phys_addr(vaddr) != Ok(frame_paddr) {
            WORKLOAD_FAILED.store(true, Ordering::Release);
            break;
        }
        match table.unmap(page, Some(false)) {
            Ok((Some(old_entry), flush)) => {
                if old_entry.leaf_address(PageLevel::Level0) != frame_paddr {
                    WORKLOAD_FAILED.store(true, Ordering::Release);
                    break;
                }
                // SAFETY: workload virtual addresses are never dereferenced
                // as data by any CPU here; only the crate's own map/unmap
                // calls ever touch them, so no TLB on any CPU can hold a
                // stale translation for this page to flush.
                unsafe { flush.ignore() };
            }
            _ => {
                WORKLOAD_FAILED.store(true, Ordering::Release);
                break;
            }
        }
    }
}

/// Entered by every AP after the trampoline reaches long mode with its
/// published stack and worker id.
#[no_mangle]
extern "C" fn ap_main(worker_id: u64) -> ! {
    AP_READY.store(true, Ordering::Release);

    let ptr = wait_for_table();
    spin_wait(|| WORKLOAD_START.load(Ordering::Acquire), "VERIOS_PAGETABLE_SMP_AP_NO_START\n");

    // SAFETY: `ptr` was published only after the table's construction and
    // identity mapping completed; the table stays alive until every worker
    // (including the BSP) has incremented `COMPLETED_WORKERS`.
    run_worker(unsafe { &*ptr }, worker_id as usize);
    COMPLETED_WORKERS.fetch_add(1, Ordering::Release);
    halt()
}

fn wait_for_table() -> *const SmpTable {
    let mut ptr = core::ptr::null_mut();
    spin_wait(
        || {
            ptr = TABLE_PTR.load(Ordering::Acquire);
            !ptr.is_null()
        },
        "VERIOS_PAGETABLE_SMP_TABLE_NOT_PUBLISHED\n",
    );
    ptr
}

/// Builds the shared table, brings up the three APs one at a time, joins the
/// concurrent map/unmap workload as worker 0, and validates the result.
#[no_mangle]
extern "C" fn bsp_main() -> ! {
    serial_init();
    serial_write("VERIOS_PAGETABLE_SMP_BOOT_START\n");
    install_trampoline();

    // `PageTable::new` direct-maps `GuestAllocator::direct_map()`'s whole
    // range while building the root, which already identity-maps the code,
    // trampoline, stacks, and table arena through the linked image end.
    // The identity range holds this guest's own code, so its leaf flags must
    // not carry NX (unlike `PTEntryFlags::data()`, meant for pure data).
    let identity_flags = PTEntryFlags::PRESENT
        | PTEntryFlags::WRITABLE
        | PTEntryFlags::ACCESSED
        | PTEntryFlags::DIRTY;
    let table = match SmpTable::new(SpinStripes::new(), identity_flags) {
        Ok(table) => table,
        Err(_) => fail("VERIOS_PAGETABLE_SMP_BUILD_FAILED\n"),
    };
    if table.validate_page_table().is_err() {
        fail("VERIOS_PAGETABLE_SMP_BUILD_INVALID\n");
    }
    serial_write("VERIOS_PAGETABLE_SMP_BUILD_OK\n");

    configure_apic(&table);

    let root = table.root_paddr();
    if root.bits() > u32::MAX as usize {
        fail("VERIOS_PAGETABLE_SMP_ROOT_TOO_HIGH\n");
    }
    load_cr3(root.bits());
    AP_ROOT_PA.store(root.bits() as u64, Ordering::Release);
    serial_write("VERIOS_PAGETABLE_SMP_CR3_OK\n");

    for apic_id in 1..=AP_COUNT as u32 {
        start_ap(apic_id);
        serial_write("VERIOS_PAGETABLE_SMP_AP_UP\n");
    }

    // SAFETY: every AP is parked waiting for `TABLE_PTR`/`WORKLOAD_START`, so
    // this is the only writer; the table stays reachable until every worker
    // finishes and increments `COMPLETED_WORKERS`.
    let storage = core::ptr::addr_of_mut!(TABLE_STORAGE);
    unsafe {
        (*storage).write(table);
        TABLE_PTR.store((*storage).assume_init_mut() as *mut SmpTable, Ordering::Release);
    }
    WORKLOAD_START.store(true, Ordering::Release);
    serial_write("VERIOS_PAGETABLE_SMP_WORKLOAD_START\n");

    let table_ref = unsafe { &*TABLE_PTR.load(Ordering::Acquire) };
    run_worker(table_ref, 0);
    COMPLETED_WORKERS.fetch_add(1, Ordering::Release);

    spin_wait(
        || COMPLETED_WORKERS.load(Ordering::Acquire) == NUM_WORKERS,
        "VERIOS_PAGETABLE_SMP_WORKERS_TIMEOUT\n",
    );
    serial_write("VERIOS_PAGETABLE_SMP_WORKLOAD_DONE\n");

    if WORKLOAD_FAILED.load(Ordering::Acquire) {
        fail("VERIOS_PAGETABLE_SMP_WORKLOAD_FAILED\n");
    }
    for worker_id in 0..NUM_WORKERS {
        let vaddr = VirtAddr::from(WORKLOAD_BASE_VA + worker_id * Regular::SIZE);
        if table_ref.phys_addr(vaddr) != Err(PagingError::NotMapped) {
            fail("VERIOS_PAGETABLE_SMP_STALE_MAPPING\n");
        }
    }
    if table_ref.validate_page_table().is_err() {
        fail("VERIOS_PAGETABLE_SMP_FINAL_INVALID\n");
    }

    // SAFETY: every worker (including this one) has returned, so no software
    // or hardware use of the table remains; `assume_init_read` moves it out
    // without dropping the storage, matching the single ownership transfer
    // `leak` requires.
    let owned_table = unsafe { (*core::ptr::addr_of!(TABLE_STORAGE)).assume_init_read() };
    let leaked_root = owned_table.leak().1;
    if leaked_root != root {
        fail("VERIOS_PAGETABLE_SMP_ROOT_CHANGED\n");
    }
    serial_write("VERIOS_PAGETABLE_SMP_BOOT_OK\n");
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
    fail("VERIOS_PAGETABLE_SMP_PANIC\n")
}
