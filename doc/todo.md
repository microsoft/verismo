# 5. TODO

Open work, grouped by the component it belongs to.

## Machine model

* [ ] Model reserved-bit and CPUID-capability preconditions for control-register
      and MSR writes; today only a successful write is modeled.
* [ ] Model segment and descriptor-table operations.
* [ ] Model faults, so that a failed operation is a modeled outcome rather than
      an unstated precondition.
* [ ] Define the memory permission model
      ([§1.3](machine-model.md#13-memory-model)) and relate it to `paging_inv`.
* [ ] Decide whether `AsmRegisterPointsTo` stays conceptual or becomes the
      interface to a future assembly-level verifier.

## Paging view

* [ ] Relate `PagingView` to the page-table walk, so the register preconditions
      and the translation are one statement.

## Allocator

* [ ] Verify range disjointness for the virtual-address allocator
      ([§2.1](allocator.md#21-virtual-memory-allocator)); neither tree proves it
      yet.
* [ ] Re-state the physical allocator's contract against the shared memory model
      rather than per-project permission types.
* [ ] Shrink the trusted `GlobalAlloc` shim in
      `source/verismo/src/allocator/trusted.rs`, or document why the
      `Tracked::assume_new()` seam is acceptable.
* [ ] Reconcile VeriSMo's single-permission design with COCONUT-SVSM's split of
      data and shared read-only metadata permissions.

## Page table

* [ ] Specify and verify the walk relation, then `map`/`unmap`/`protect`.
* [ ] Model TLB invalidation and tie it to the walk relation; verios-pagetable
      leaves flushing to the host, so the obligation has to land somewhere.
* [ ] State the security properties of
      [§3.2](page-table.md#32-security-properties) over the reachable entry set.
* [ ] Decide how `source/paging` and `~/verios-pagetable` relate: one is the
      generic verified table, the other should not duplicate it.
* [ ] Discharge the `os_contract` obligations from the verified allocator rather
      than assuming them.
* [ ] Resync the vendored COCONUT-SVSM code when upstream moves:
      `paging/src/{address,util,sizes}.rs`, `paging/src/specs/{address,
      address_inner,align,external,nonnull}.rs`, `paging/src/proofs/{align,
      sizes}.rs` and `common_proofs/src/bits.rs`. Only the lemmas these crates
      use were kept, so an upstream resync should re-trim rather than re-import
      the whole helper crates.

## Scheduler

* [ ] Choose the proof framework for liveness and fairness, and define its
      interface to the Verus safety proofs.
* [ ] State the environment fairness assumptions as an explicit trusted
      interface.
* [ ] Specify context switch as a register-token transfer that preserves
      `rust_abi_wf`.
