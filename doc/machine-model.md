# 1. Machine model

Crate: `source/machine_model`.

The trusted model of the architectural state that compiled Rust code runs
against. Everything here is assumed, not proved, so it is kept small, sealed and
reviewable: it is the base every other component's proof rests on.

## 1.1 Register state

*Status: partial.*

`RegisterState` holds one ownership token per modeled register, so a claim about
a register is a claim about the token that owns it, and two pieces of code
cannot both believe they control the same register.

### Two token layers

* `AsmRegisterPointsTo<R>` — the view *inside* an `asm!` block. Opaque and
  unconstrained. Only trusted `external_body` functions mention it. Verus cannot
  verify assembly, so this layer is conceptual: it marks where the model stops.
* `RustRegisterPointsTo<R>` — the token Rust code actually holds. It wraps the
  asm token and carries `R::rust_abi_wf` as a `#[verifier::type_invariant]`.

The split exists because the two contexts genuinely differ. Inside an `asm!`
block a register may hold anything; the moment control returns to Rust, the
compiler is entitled to assumptions it never checks.

### The Rust ABI contract

`rust_abi_wf` states what compiled Rust may assume about a register. Today the
only non-trivial case is `Rflags`: `DF` is clear. The Rust reference guarantees
this at every `asm!` boundary (`asm.rules.x86-df`, which covers x86 and x86-64),
and rustc emits no `cld` — it *assumes* DF is clear rather than establishing it.
Hardware does not clear DF on interrupt or exception entry, which is why the
entry stubs (`verismo/src/entry.s`, `verismo_main/src/entry.s`) must `cld`
themselves.

Because this is an ABI property rather than a hardware one, it is defined per
target under `src/arch/`, and the whole `arch::x86_64` module is gated on
`target_arch = "x86_64"`.

### Sealing

Register markers (`Cr0`, `Rflags`, `Msr`, …) implement `RegSpec`, which is
public but sealed by a crate-private supertrait. Sealing is what keeps the model
trusted: a downstream crate cannot add a marker, and therefore cannot extend
`ReadableReg` or `ControlReg` either. It stays *nameable* so that downstream
crates can still use `R::Value`.

### MSRs

Fixed registers are identified by their marker type, so a `RustRegisterPointsTo<Cr0>`
can only ever be about CR0. MSRs are identified by a runtime number, so their
tokens live in `MsrMap`, whose private map carries a type invariant: a token
stored under key `n` always owns MSR `n`.

Access is `remove` / write / `insert`; `insert` requires the token's register
number to match its key. No `borrow_mut` is exposed, since a `&mut` token
escaping the invariant check would let a caller substitute a token for a
different MSR and silently break key agreement.

### Verified operations

Control-register read/write, MSR read/write, `stac`/`clac`. Control-register
writes promise that only the *status* flags of RFLAGS change, which is what
preserves `IF`, `DF`, `IOPL` and `AC` across them — leaving all of RFLAGS
unconstrained would lose exactly the flags other proofs depend on.

Open: reserved-bit and CPUID-capability preconditions on writes; segment and
descriptor-table operations; a model of faults.

## 1.2 Paging view of register state

*Status: partial.* Module: `source/paging/src/structs/reg_contract.rs`.

Paging correctness depends on register state the page tables do not describe:
`CR0.PG/PE/WP`, the `CR3` frame and PCID, `CR4.PAE/PCIDE/LA57`,
`EFER.LME/LMA/NXE`, and the current CPL.

`paging_view(registers)` projects exactly those values into a `PagingView`, and
`paging_inv(registers)` states the architectural preconditions under which the
page tables have their intended meaning.

Projecting rather than duplicating matters: a view derived *from* a
`RegisterState` cannot drift from the state it describes, whereas a free-standing
ghost record has to be re-tied to the right state at every use — and nothing
catches it when a caller threads the wrong one.

Writes to `CR0`, `CR3`, `CR4` or `MSR_EFER` can invalidate this invariant, so
those operations do not preserve it; callers re-establish it.

The address widths are supplied by the host through `ArchPagingGeometry`
(`phys_addr_width`, `page_offset_width`), a supertrait of `ArchPagingMeta`, so
`cr3_paging_precondition` is stated against the embedder's geometry rather than
against fixed constants. `geometry_wf` states the sanity condition on those
widths in the crate, so a host cannot weaken it.

Open: the view is not yet related to the page-table walk.

## 1.3 Memory model

*Status: planned.*

Goal: a permission model for physical and virtual memory that composes with the
register model, so that "this pointer is safe to dereference" is a *consequence*
of the page tables and the allocator rather than an assumption.

The pieces that must fit together:

* raw physical frames, owned as permissions and handed out by the physical
  allocator;
* virtual addresses, whose dereferenceability is derived from the mapping plus
  `paging_inv`;
* aliasing — two virtual addresses mapping one frame must be visible in the
  model, since that is where memory-safety arguments usually break;
* confidentiality bits (the SNP C-bit) as part of the address rather than an
  afterthought: a private and a shared mapping of the same frame are different
  memory, and treating them as one is a real vulnerability, not a modeling
  detail.

Prior art in-tree: `source/verismo/src/mem` (`rawmem_p.rs`, `rawmem_s.rs`) and
VeriSMo's `SnpPointsToRaw`. COCONUT-SVSM's `alloc_perms.verus.rs` is the same
idea applied to a heap.
