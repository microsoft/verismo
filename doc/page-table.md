# 3. Verified page table

Primary reference: **verios-pagetable** (`~/verios-pagetable`) — a concurrent
page table written in Rust and verified with Verus, embedded into Linux,
COCONUT-SVSM and litebox. Its `docs/CONCURRENCY.md` is the detailed spec of what
may run concurrently; this document records the design and how it relates to the
machine model here.

Also in this repository: `source/paging` (`PageLevel`, `PageTableEntry<A>`,
`ArchPagingMeta`, `os_contract`, `UniqueAddress`, and the address types
`address.rs` / `util.rs` / `sizes.rs` vendored from COCONUT-SVSM) and the prototypes in
`source/concurrent_rw/tests/src/pt.rs` and `pt2.rs`. The legacy version is
`source/verismo/src/pgtable_e`.

## Design

Two levels of exclusion, from the verios-pagetable README:

* **Outer, shared or exclusive.** `map`, `unmap`, `protect` and `query` only
  walk or grow the tree and are compatible with each other, so they take the
  shared side. `free_range` unlinks interior tables and returns their pages, so
  it takes the exclusive side — a walker must not be standing in a page that is
  being freed.
* **Inner, per table page.** Under the shared side, two cores growing the same
  interior entry would both see it empty and both publish a child, so a slot's
  read-modify-write happens under a lock for its table page, supplied by the
  host through `PtPageOps::lock`. A slot *read* takes no lock: it re-reads under
  the lock before acting, so the optimistic read only chooses the path.

**The host is a contract.** `src/host.spec.rs` states what an embedder must
provide — page allocation, the per-page lock, address translation. It is a
marker trait in the kernel build and a set of proof obligations under Verus, so
each host discharges them in its own verification. That is what makes one
verified page table embeddable in three very different systems, and it is the
same shape as `os_contract.rs` in `source/paging`.

Architecture geometry (level count, entry encoding, page size, address and
confidentiality masks) is a parameter — `arch/` in verios-pagetable,
`ArchPagingMeta` in `source/paging` — not a constant.

## 3.1 Functional correctness

*Status: partial.*

The page table implements the translation it claims: `map`, `unmap` and
`protect` change the translation exactly on the affected range and nowhere else,
across all levels, including huge leaves and the split of a partially covered
huge leaf into a table of finer leaves with the same frames and protection.

Range operations are loops of the single-entry operation, so their correctness
reduces to the single-entry case plus a frame condition on the rest of the
address space.

Two actors complicate every postcondition, and both are modeled rather than
assumed away:

* the **hardware walker**, which may set accessed/dirty bits on any present
  entry at any time — so every reported entry word is a receipt modulo
  environment drift (`entry_env`), not an exact value;
* the host's **foreign words** (nonzero and non-present: swap or migration
  entries). The crate observes and reports them, and never writes or clears
  them.

Open in `source/paging`: the walk relation itself, the operations, and TLB
invalidation. TLB visibility is deliberately outside the page table's contract
in verios-pagetable — operations return the old words and the host flushes.

## 3.2 Security properties

*Status: planned.*

Beyond functional correctness, the properties that actually protect the guest.
All of them are statements about the *reachable* entry set, so they depend on
§3.1's walk relation:

* no unintended aliasing of a private frame into a shared mapping, and the C-bit
  discipline of `make_private_address` / `make_shared_address` holds for every
  reachable entry;
* W^X: no mapping is simultaneously writable and executable;
* privilege separation: user-accessible mappings are exactly those intended.
  This is where the register model connects — `CR4.SMEP`/`SMAP`, `RFLAGS.AC` and
  the verified `stac`/`clac` of
  [§1.1](machine-model.md#11-register-state) decide whether a user mapping is
  reachable from kernel code at all;
* every reachable mapping is backed by a frame the allocator actually granted
  ([§2.2](allocator.md#22-physical-memory-allocator)).

## 3.3 Concurrency correctness

*Status: partial.* See `~/verios-pagetable/docs/CONCURRENCY.md` for the full
matrix; the invariants it is built on are:

* **WORD** — every entry access is one aligned atomic `u64`; a reader sees the
  old or the new word, never a torn one.
* **LOCK** — one host lock per table page; all writers of a page serialize.
* **PIN** — a slot holding a table entry is frozen: nothing but `free` changes
  it, so lock-free descent through it stays valid.
* **PUBLISH** — a new subtree is built while unpublished and made visible by a
  single release store, so no walker ever sees a half-built table.
* **RECHECK** — every writer re-reads the slot under the lock and acts on what
  is actually there.
* **FENCE** — `free` requires host exclusion of the whole range, lookups
  included. There is no RCU grace period by design, so exclusion is the only
  thing that permits reclaiming a page under lock-free readers.

The reason these are invariants rather than proof steps: the hardware walker
cannot be blocked, so an update sequence must be safe at *every* intermediate
store, not merely at its end. PUBLISH and PIN are what make that true, and they
are also why break-before-make and ordering table linking after frame
initialization are correctness requirements rather than conventions.

The ownership protocol is a token/state-machine argument: `mrsw_tokens` in
verios-pagetable, `source/concurrent_rw` here.
