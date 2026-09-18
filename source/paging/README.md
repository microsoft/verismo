# Paging

Verismo needs to modify active page tables while other software and the MMU can
still walk them. It must also split huge mappings, change confidential-memory
address tags, share selected subtrees between roots, and reclaim owned table
pages without relying on one global lock.

Many page-table APIs assume a simpler environment: exclusive mutable access to
the whole tree, architecture-specific invalidation performed out of band, and
uniform ownership of every reachable table page. Those assumptions do not fit a
security monitor whose mappings remain live during concurrent updates.

This crate exists to put those requirements in the paging interfaces instead of
leaving them as conventions at each call site.

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

The sequential and concurrent controllers retain different borrowing and
locking models but share mapping and architecture-transition semantics.
Break-before-make and flush policy live below both controllers so they cannot
drift between implementations. See [concurrency.md](concurrency.md) for the
complete locking, lifetime, reclamation, and TLB contracts.

This crate is most useful when page tables are live, shared, confidential-memory
tags matter, or failure and flush behavior must be explicit. A smaller
architecture-specific crate may be preferable for a boot-time-only table that
is built under exclusive ownership and never modified concurrently.

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
