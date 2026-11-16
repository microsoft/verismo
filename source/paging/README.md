# verios-pagetable-beta

`verios-pagetable-beta` is an independent paging crate developed as part of
Verismo. It was built for systems that modify active page tables while other
software and the MMU can still walk them. Such systems must also split huge
mappings, change confidential-memory address tags, share selected subtrees
between roots, and reclaim owned table pages without requiring one global lock.

Many page-table APIs assume a simpler environment: exclusive mutable access to
the whole tree, architecture-specific invalidation performed out of band, and
uniform ownership of every reachable table page. Those assumptions do not fit a
security monitor whose mappings remain live during concurrent updates.

This crate exists to put those requirements in the paging interfaces instead of
leaving them as conventions at each call site.

## Public API

Imports are grouped into five namespaces, without exposing implementation submodules:

- `paging::arch::x86_64`: paging parameters, entry flags, CR3/CR4 access, and x86-64 flush tokens.
- `paging::address`: physical/virtual addresses and alignment helpers.
- `paging::pagetable`: controllers, CPU-local bindings, and switching results.
- `paging::structs`: entries, pages, frames, levels, sizes, ownership policies, and contracts.
- `paging::tlb`: architecture-independent flush obligations.

Examples and tests can import the needed groups directly:

```rust
use paging::{
    address::{PhysAddr, VirtAddr},
    arch::x86_64::{PTEntryFlags, X86_64Paging, X86_64PagingParams},
    pagetable::KernelPageTable,
    structs::{Lvl, PagingAllocator},
    tlb::MayNeedFlush,
};
```

## Source organization

Paging types keep lifecycle operations in a consistent reading order:

1. Struct and supporting type declarations.
2. Constructors and adoption functions.
3. Consuming operations, teardown functions, and `Drop`.
4. Other associated functions without a receiver.
5. Shared-receiver (`&self`) operations.
6. Mutable-receiver (`&mut self`) operations.

Trait implementations and free helpers follow the inherent implementations.
When different bounds require multiple `impl` blocks, the blocks still follow
this order rather than grouping by generic signature.

## Why use this crate

| Concern | Guarantee provided here |
| --- | --- |
| Page-size correctness | `Page<PS>`, `PhysFrame<PS>`, and `PageRangeInclusive<PS>` make virtual and physical granularity explicit in types. |
| Concurrent live walks | Walkers use pinned page pointers and atomic entry snapshots rather than whole-page shared or mutable references. |
| Update locking | Updates lock by clean physical table-page key and never hold two content locks. Select one global lock or 64 stripes through crate features. |
| Safe publication | New paths and split subtrees are completely initialized before their parent descriptor becomes visible. |
| Architecture ordering | Structural and output-address transitions consult `requires_break_before_make`; ordinary permission updates remain a distinct valid-to-valid path. |
| TLB obligations | Mutations return `#[must_use]` `MayNeedFlush` values unless the operation completed its required synchronous maintenance. |
| Partial failure | Range mapping retains a successful prefix and reports the remaining work in equivalent 4 KiB pages. |
| Mixed mappings | Adjacent 2 MiB and 4 KiB ranges are mapped explicitly rather than inferred from alignment or frame addresses. |
| Ownership and reclamation | Policies distinguish owned and borrowed root entries; cleanup requires exclusive ownership and explicit hardware quiescence. |
| Canonical addresses | Range iteration and adjacency handle the low/high canonical seam without traversing the noncanonical hole. |
| Accessed/dirty history | Atomic valid-entry updates preserve racing A/D bits by default; `ignore_access_dirty_bits` makes discarding them an explicit build policy. |

The controller combines atomic walks with explicit content locking.
Break-before-make and flush policy remain below the controller so every update
path uses the same architecture-transition semantics. See
[concurrency.md](concurrency.md) for the complete locking, lifetime,
reclamation, and TLB contracts.
See [structs/struct.md](src/structs/struct.md) for the tree representation,
lifecycle and ownership typestates, and reclamation diagrams.

This crate is most useful when page tables are live, shared, confidential-memory
tags matter, or failure and flush behavior must be explicit. A smaller
architecture-specific crate may be preferable for a boot-time-only table that
is built under exclusive ownership and never modified concurrently.

`PageTable::new_empty` allocates an unmapped root with the selected ownership
policy. Unlike the direct-mapped `KernelPageTable::new`, it needs only a
`PagingAllocator`; the embedder establishes mappings before activating the root.
It does not relax the self-mapping checks on imported roots or change the
ownership, sharing, and hardware-quiescence requirements.

## Built-in lock selection

Content locks are internal; there is no lock-provider trait or metadata type
parameter. Construct `KernelPageTable<Arch, Alloc, Lvl<3>>::new_empty()`, or select
owned root slots through `UserPageTable<Arch, Alloc, Lvl<3>, Owned>`.

| Paging features | Mutex | Granularity |
| --- | --- | --- |
| None | `spin::mutex::TicketMutex` | One global lock |
| `spin-mutex` | `spin::mutex::SpinMutex` | One global lock |
| `striped-locks` | `spin::mutex::TicketMutex` | 64 locks |
| `spin-mutex`, `striped-locks` | `spin::mutex::SpinMutex` | 64 locks |

Features are additive: another consumer enabling one selects it for the shared
paging dependency. Locks are allocation-free and shared across roots. Stripes
use the clean physical table-page number modulo 64, so shared pages select the
same lock; unrelated pages can collide. Walks remain lock-free.

Neither mutex disables interrupts. Callers must prevent reentrant acquisition
and provide hardware quiescence separately. Kernels needing shootdown progress
while waiting can enable `lock-wait-hook` and supply a non-unwinding
`extern "C" fn paging_lock_wait()` symbol. It runs within the mutex's genuine
wait loop, preserving ticket order, and must be safe in every waiting context
without acquiring locks or re-entering paging. See [concurrency.md](concurrency.md).

The comparison benchmark names the current adapter by its compiled mutex and
granularity, for example `paging-current-ticket-striped`. Its auxiliary-memory
figure charges the fixed shared lock array once, not once per worker. Historical
`paging-current` measurements used a custom per-page provider and are not
measurements of these new configurations.

## Hardware root activation

`arch/x86_64/regs.rs`, exposed as `paging::arch::x86_64`, provides privileged
`machine_model`'s `Cr3`/`Cr4` register types and values. Paging calls their
token-free `read`/`write` methods directly, without additional wrappers or
verification annotations.
Root-register flags are raw `usize` bits: PWT/PCD with CR4.PCIDE off, or a
12-bit PCID and optional bit-63 no-flush command with CR4.PCIDE on.
`cr3_flags(cr4, level, pcid, no_flush, write_through, cache_disable)` accepts
`Cr4Value`, selects the encoding, checks LA57 against the root level,
and rejects fields incompatible with PCIDE. It does not read hardware.
It returns `machine_model`'s `Cr3Value`, re-exported from `paging::arch::x86_64`;
pass `.bits() as usize` to activation or combine `Cr3Value::PWT | Cr3Value::PCD`.
Managed activation trusts callers to supply a compatible hardware paging mode
and flags valid for the current CR4.PCIDE setting and retained translations.
`RootRegisterAccess` uses `read_root_pa() -> PhysAddr` and
`store_root_pa::<L>(root, flags) -> Result<(), PagingError>`, without a
register-value type or runtime level argument. Activation supplies `L` from the
controller type; the caller must ensure the hardware paging mode matches.
Root reads strip register flags and confidentiality tags; binding identity is
the clean physical address, not a particular PCID or cache-control setting.
`ArchPagingMeta::decode_physical_address(value)` shares that address-field
decoding with PTEs; leaf frame bases still require level-specific attribute clearing.
The platform still supplies valid confidentiality tags, hardware addresses,
CPU affinity, interrupt/preemption discipline, and compatible retained translations.

`unsafe ActivePageTable::from_current_cpu()` adopts and validates the existing
kernel-owned root without rewriting its register. It permits shared-receiver mutations,
but no mutable-controller access, and is neither `Send` nor `Sync`.
`unsafe active.switch_to(next, flags)` validates and installs the target root,
returning the new binding and a
`RetiredPageTable` for the old root. Errors retain the supplied resources.

Switching is CPU-local: the retired root can still be used by other CPUs or
cached page walks, global translations, and PCIDs. Only after full hardware
exclusion and invalidation may `unsafe retired.into_page_table()` recover the
controller for cleanup or destruction. Dropping either binding retains its
allocations and borrowed shares; there is no implicit CR3 restoration or reclamation.
Root-register-hook unwinding likewise retains a possibly installed target.

Both wrappers contain a `Live` tree. Hardware activation is separate from tree
access state and ownership policy; it is a trusted unsafe boundary, not a Verus
proof. Raw register helpers support externally managed/SMP roots, whose lifetime
remains the caller's responsibility.

## Hardware boot test

The x86_64 PVH guest in `tests/kvm` enters long mode, constructs a fresh
four-level table through a high-half nonidentity direct map, identity-maps the
loaded image (including static locks in BSS), adds a separate 4 KiB virtual alias,
then loads the constructed root into CR3. A serial `VERIOS_PAGETABLE_BOOT_OK`
marker is emitted only after values written to a probe page through the bootstrap identity map are
observed through the new table's high direct map, a write through the extra
alias reaches that page, and the loaded image's text and read-only data match
their high direct-map aliases. The embedded image signature must also have its
expected binary content.

Run it from `source`:

```console
paging/tests/kvm/run.sh
```

The runner boots QEMU and Cloud Hypervisor when they are available and requires
every attempted VMM to pass. QEMU uses KVM when `/dev/kvm` is accessible and
otherwise falls back to TCG. Cloud Hypervisor is skipped without KVM because it
has no software-emulation mode. The guest uses the Xen PVH direct-boot ABI so
both VMMs can load the same ELF without external BIOS or UEFI firmware.

### Four-CPU concurrent boot test

The second PVH guest, `tests/kvm/smp_guest.rs`, boots four CPUs and exercises
one shared `PageTable`. The BSP builds the table with the crate's selected mutex
and granularity, then
brings up three APs one at a time: before each SIPI it publishes that AP's
stack top and worker id, sends INIT/deassert/SIPI through the x2APIC MSR
interface (falling back to the legacy MMIO-mapped local APIC on hosts whose
QEMU/TCG predates x2APIC MSR support) and waits for the AP to reach Rust
before moving on, so trampoline state is never written for two APs at once.
The real-mode trampoline itself is linked at its ordinary address like any
other code and copied to the fixed low physical scratch address SIPI
requires only once the BSP is running: QEMU's PVH direct-boot loader
miscopies images whose PT_LOAD segments sit at addresses far apart, so the
trampoline cannot simply be linked at that low address directly.

Once every AP is up, the BSP publishes the shared table and releases all four
CPUs into a bounded (512-round) workload: each worker repeatedly maps its own
4 KiB page, verifies the software translation, unmaps it, and confirms the
removed entry matched what it installed. Every worker's page lives in the
same 2 MiB region, so the shared intermediate tables down to the leaf level
are built and contended for by all four CPUs, exercising concurrent
structural growth alongside entry updates. The flush obligation each unmap
returns is discharged with `unsafe { flush.ignore() }`: this is sound because
the workload's virtual addresses are never dereferenced as data by any CPU,
only ever touched through the crate's own map/unmap calls, so no TLB can hold
a stale translation for them to invalidate. For the same reason the
architecture's flush hooks stay purely local, as in the single-CPU guest.
After every worker finishes, the BSP confirms all four pages are unmapped and
the table is still structurally valid, then leaks it and emits
`VERIOS_PAGETABLE_SMP_BOOT_OK`. Every stage (build, CR3 load, each AP's
startup, workload start/completion) has its own serial marker, and every
bounded wait has a distinct timeout marker, to make a stuck boot or a stuck
AP diagnosable from the serial log alone.

Run it from `source`:

```console
paging/tests/kvm/run-smp.sh
# Select a different built-in lock algorithm and granularity:
GUEST_FEATURE=kvm-smp-test,spin-mutex,striped-locks paging/tests/kvm/run-smp.sh
```

It uses the same runner as the single-CPU test (`run.sh`, parameterized by
environment variables for the guest example, linker script, Cargo feature,
success marker, and vCPU count), so it has the same KVM/TCG and
Cloud-Hypervisor-needs-KVM behavior, just with `-smp 4` (`--cpus boot=4` for
Cloud Hypervisor).

## Live page-table entry access

`PTPage` always stores entries as `AtomicUsize`. Ignoring hardware-maintained
accessed and dirty bits permits software updates to discard those bits; it does
not make plain Rust access to a live entry safe. The MMU remains an external
observer that the Rust abstract machine does not model as a thread.

Plain reads and writes can cause these bugs:

- **Eliminated updates:** a PTE store can be removed when no Rust-visible read
  observes it, even though the MMU must observe it.
- **Collapsed break-before-make:** the compiler can merge an invalidating store
  followed by a replacement store, removing the required invalid interval.
- **Premature publication:** child-table initialization can move after the
  parent descriptor is published, exposing an incomplete table.
- **Stale observations:** repeated reads can be reused or hoisted while hardware
  changes the entry.
- **Incorrect maintenance order:** PTE accesses can move across TLB maintenance
  or architecture barriers unless those operations impose compiler ordering.

Naturally aligned native-width loads and stores are normally indivisible on
x86-64 and AArch64, but this hardware property does not give ordinary or
volatile Rust access atomic memory-model semantics. Volatile access prevents
elimination and merging, but it does not synchronize software threads or make a
read-modify-write sequence atomic.

Use atomic access for every live PTE. Relaxed atomics are suitable when only
single-access visibility and atomicity are required; publishing initialized
tables and coordinating lock-free software walkers require the corresponding
release/acquire ordering. Architecture-mandated barriers and TLB maintenance
remain separate obligations.

Plain access through `AtomicUsize::get_mut()` is appropriate only while a table
is private and unpublished, or while all software aliases and hardware walkers
are quiesced. It has the same optimized access cost as plain `usize` storage.
