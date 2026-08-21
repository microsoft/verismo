# Design: verified OS components

Design notes for the verified operating-system components, one document per
topic. Each document states the goal, what exists today, and what is open.

Status: **done** — verified in CI; **partial** — verified but incomplete;
**planned** — not started.

| # | Topic | Document | Status |
|---|---|---|---|
| 1 | Machine model | [machine-model.md](machine-model.md) | partial |
| 1.1 | Register state | [machine-model.md](machine-model.md#11-register-state) | partial |
| 1.2 | Paging view of register state | [machine-model.md](machine-model.md#12-paging-view-of-register-state) | partial |
| 1.3 | Memory model | [machine-model.md](machine-model.md#13-memory-model) | planned |
| 2 | Verified allocator | [allocator.md](allocator.md) | partial |
| 2.1 | Virtual memory allocator | [allocator.md](allocator.md#21-virtual-memory-allocator) | partial |
| 2.2 | Physical memory allocator | [allocator.md](allocator.md#22-physical-memory-allocator) | partial |
| 3 | Verified page table | [page-table.md](page-table.md) | partial |
| 3.1 | Functional correctness | [page-table.md](page-table.md#31-functional-correctness) | partial |
| 3.2 | Security properties | [page-table.md](page-table.md#32-security-properties) | planned |
| 3.3 | Concurrency correctness | [page-table.md](page-table.md#33-concurrency-correctness) | partial |
| 4 | Verified task scheduler | [scheduler.md](scheduler.md) | planned |
| 4.1 | Liveness | [scheduler.md](scheduler.md#41-liveness) | planned |
| 4.2 | Fairness | [scheduler.md](scheduler.md#42-fairness) | planned |
| 4.3 | Concurrency | [scheduler.md](scheduler.md#43-concurrency) | planned |
| 5 | TODO | [todo.md](todo.md) | — |

## Related work in other trees

Three of these components are already verified elsewhere, in code this
repository either hosts, embeds, or draws its design from:

* **VeriSMo** (`source/verismo`) — the SEV-SNP monitor in this repository. Its
  allocator and page-table code are the first-generation proofs.
* **COCONUT-SVSM** (`~/svsm`) — the upstream SVSM, whose memory allocator is
  verified with Verus in `kernel/src/mm/*.verus.rs`.
* **verios-pagetable** (`~/verios-pagetable`) — a standalone concurrent page
  table verified with Verus, embedded into Linux, COCONUT-SVSM and litebox.

The documents here describe the *next* model: one trusted machine model that all
of these components build on, rather than one per project.
