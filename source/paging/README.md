# verios-pagetable-beta

`verios-pagetable-beta` is an independent paging crate developed as part of
Verismo. It was built for systems that modify active page tables while other
software and the MMU can still walk them. Such systems must also split huge
mappings, change confidential-memory address tags, share selected subtrees
between roots, and reclaim owned table pages without relying on one global lock.

Many page-table APIs assume a simpler environment: exclusive mutable access to
the whole tree, architecture-specific invalidation performed out of band, and
uniform ownership of every reachable table page. Those assumptions do not fit a
security monitor whose mappings remain live during concurrent updates.

This crate exists to put those requirements in the paging interfaces instead of
leaving them as conventions at each call site.

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
| Update locking | The concurrent controller locks only the table page being edited and never holds two potentially aliased content locks. |
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

This crate is most useful when page tables are live, shared, confidential-memory
tags matter, or failure and flush behavior must be explicit. A smaller
architecture-specific crate may be preferable for a boot-time-only table that
is built under exclusive ownership and never modified concurrently.

## Hardware boot test

The x86_64 PVH guest in `tests/kvm` enters long mode, constructs a fresh
four-level table through a high-half nonidentity direct map, adds the low
bootstrap identity mapping and a separate 4 KiB virtual alias, then loads the
constructed root into CR3. A serial `VERIOS_PAGETABLE_BOOT_OK` marker is emitted
only after values written to a probe page through the bootstrap identity map are
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
one shared `PageTable`. The BSP builds the table with a minimal striped spin
mutex satisfying its `LockSpec`, then
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
