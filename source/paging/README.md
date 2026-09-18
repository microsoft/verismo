# Paging

This crate provides typed page-table construction, translation, mapping, and
TLB-maintenance interfaces for sequential and concurrent controllers.

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
