# 2. Verified allocator

Two allocators have been verified in this line of work — VeriSMo's in
`source/verismo/src/allocator`, and COCONUT-SVSM's in `~/svsm`
(`kernel/src/mm/*.verus.rs`). This document records how each was done and what
the shared design should be.

Both are physical/page allocators. The virtual-address side is thinner in both
trees, and is the larger gap.

## How the two existing allocators are verified

### VeriSMo

`source/verismo/src/allocator` — a linked-list allocator (`LinkedListAllocator`,
the one wired up as `VeriSMoAllocator`) and a buddy allocator
(`BuddyAllocator`), behind a `VSpinLock`.

* The unit of ownership is `SnpPointsToRaw`: a tracked permission for a raw byte
  range, carrying its address, size and the SNP validation/encryption state of
  the memory. Allocation *returns* the permission along with the pointer, which
  is what makes the result usable rather than merely well-typed.
* The contract is `alloc_valid_ptr`: the returned permission covers exactly
  `(ptr, size)` and is default-initialized.
* The free list is a proof object as well as a data structure: `linkedlist.rs`
  relates the in-memory node chain to a ghost sequence, so "the list is
  well-formed" and "the permissions in it are disjoint" are one invariant.
* The `GlobalAlloc` impl in `trusted.rs` is `#[verifier::external]` and uses
  `Tracked::assume_new()`. This is the deliberate seam: Rust's global allocator
  signature has nowhere to put a permission, so the verified core is wrapped by
  a small trusted shim. Everything reached through `alloc::alloc` is therefore
  outside the proof — a reason to prefer the direct, permission-returning API.

### COCONUT-SVSM

`~/svsm/kernel/src/mm/alloc*.verus.rs` — the page allocator behind the SVSM
heap. Specs live in `.verus.rs` files `include!`d under `verus_keep_ghost`, so
the upstream source stays buildable without Verus.

The proof structure, from `alloc.verus.rs`:

* on entry to the kernel, a set of unique, trusted memory permissions is assumed
  to exist — the TCB boundary is stated once, at the top;
* permissions are unforgeable, so their integrity holds for the whole run;
* the memory region tracks both the page permissions and the permissions for the
  `PageInfo` metadata array;
* a `PageInfo` permission is *shared read-only* once its page is allocated, so
  every holder observes the same metadata — the allocator can read any page's
  info at any time without taking ownership away from the owner;
* `LinearMap` (phys↔virt) is proved correct and used for all managed memory;
* `alloc_info.verus.rs` and `alloc_types.verus.rs` prove the encode/decode of
  the packed 8-byte `PageStorageType`, which is where bit-level bugs would hide.

The interesting difference from VeriSMo: SVSM splits *data* permission from
*metadata* permission, and shares the latter fractionally. That is what lets the
allocator inspect a page it has given away.

## 2.1 Virtual memory allocator

*Status: partial.*

Allocates virtual address ranges. The property to prove is disjointness: two
live allocations never overlap, and a freed range is unreachable from any live
handle. Allocation must return a *capability* for the range, not a bare address,
or callers gain nothing from the proof.

Allocating a range is not mapping it: the VA allocator hands out address space,
the page table backs it, and the two must not be able to disagree. This is the
natural place to state that `map` is only called on VA ranges the caller owns.

Current state: COCONUT-SVSM has `virtualrange.rs` (a bitmap allocator) and
`vmalloc.rs`/`rawalloc.rs`, none of which are verified yet; VeriSMo works in
terms of typed `GVA` addresses. Neither yet proves range disjointness.

## 2.2 Physical memory allocator

*Status: partial* — verified in both trees above, not yet against the shared
memory model of [§1.3](machine-model.md#13-memory-model).

Allocates page frames. `source/paging/src/structs/os_contract.rs` already states
what the page table needs from it: every successful allocation returns a
*unique*, page-aligned, *zeroed* frame whose address is clean of
confidentiality bits, valid until freed.

Uniqueness is the hard obligation and the one the page-table proofs consume: it
is what lets a newly linked table be argued unaliased. Both existing allocators
establish it the same way — by owning a permission per frame and never
duplicating it — which is the design to keep.

The zeroing and C-bit obligations are not incidental. A frame recycled from a
private mapping into a shared one leaks guest data unless both hold.
