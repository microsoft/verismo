# SVSM kernel integration

This is an **actual SVSM kernel build and host-test integration**, not a replacement
of SVSM's boot-time page tables. The bridge constructs an owned, unpublished
Verismo tree or exclusively borrows an existing acyclic SVSM tree, using SVSM's
real page allocator and platform metadata. It adds no proof assumptions or
trusted verification specifications.

## Pinned inputs and reproduction

- SVSM: `ziqiaozhou/svsm`, commit
  `5ee2b61dfa2612dab27fe000c9e46c5b25d9a8f6`.
- Its `packit` submodule: `98411fde7ddb76061159b4abbf0487a9adba469b`.
- Rust/Cargo: SVSM's pinned **1.88.0**, target `x86_64-unknown-none`.
- Verismo: the local `source/paging` crate adjacent to these fixtures, including
  its typed `map`, `unmap`, and `set_flags` APIs, plus `split` and
  `set_flags_range`.
- `svsm-lock.patch` retains the exact dependency resolution used for validation.

From the Verismo repository:

```sh
export SVSM_SOURCE=/path/to/existing/svsm
export SVSM_CHECKOUT=/path/to/separate/local/svsm-integration
python3 source/paging/compat/svsm/reproduce.py
```

`SVSM_SOURCE` must contain the pinned commit and initialized, pinned `packit`.
The script never writes to it. It clones locally using `git clone --shared`,
checks the pins, applies `svsm.patch` and `svsm-lock.patch`, copies `adapter.rs`
and `tests.rs` into the clone's kernel, and runs the commands below. Existing
unrelated changes are rejected. Reruns validate the complete patched contents,
including both copied Rust files, without overwriting edits. Staged changes and
modified submodules are also rejected; use a fresh clone for updated fixtures.
`--prepare-only` applies the integration without compiling.

Do not set `RUSTFLAGS` or `CARGO_ENCODED_RUSTFLAGS`: those override SVSM's target
configuration, including its required software AES/POLYVAL selection. The patch
adds Verismo's `target_min_page="4kib"` to the existing target configuration
without replacing those settings.

After preparation, the exact validation commands in the clone are:

```sh
cargo test --locked -p svsm-paging --test pgtable
cargo test --locked -p svsm --lib 'mm::' --no-default-features
SVSM_VERISMO_SUPPRESS_GLOBAL=1 \
  cargo test --locked -p svsm --lib 'mm::verismo_paging::tests' --no-default-features
cargo check --locked -p svsm --lib --bins --no-default-features \
  --target x86_64-unknown-none
cargo build --locked -p svsm --bin svsm --no-default-features \
  --target x86_64-unknown-none
```

Full reproduction completed on 2026-09-14:

| Command | Result |
| --- | --- |
| Original SVSM `pgtable` tests | 10 passed; 3 existing unnecessary-`unsafe` warnings |
| SVSM kernel memory tests | 37 passed, 1 existing guest-only test ignored |
| Bridge with SVSM `GLOBAL` suppression | 1 passed |
| Bare-metal kernel library and binary check | Passed |
| Bare-metal kernel binary build/link | Passed |

Latest targeted run (2026-09-15): `mm::verismo_paging::tests` passed with both
`GLOBAL` policies, and the bare-metal library/binary check and kernel build/link
passed.

Stateless-allocator validation includes the public `DirectMappedAllocator`
provider and verifies its global mapping identity and allocation accounting.

The same targeted command passed again on Rust 1.88.0 after enabling recursive
owned-tree destruction (2026-09-16), including restored allocator accounting
after owned teardown and preservation of borrowed native tables.

The resulting ELF is `target/x86_64-unknown-none/debug/svsm`. No VM was booted.
The working clone and build outputs remain under the session's
`files/integrations/svsm` directory; the original SVSM worktree remains clean.
No commits or pushes are performed.

## What is actually connected

`adapter.rs` is installed as `kernel/src/mm/verismo_paging.rs`. It uses:

- SVSM `PhysAddr`, `VirtAddr`, `PTEntryFlags`, `MemoryRegion`, and `PageSize` at
  its caller interface; Verismo-specific addresses stay behind the bridge.
- `PageBox::<SVSM PTPage>::try_new_zeroed()` and SVSM's actual allocator.
  This adapter still returns initialized native pages, but Verismo does not
  require allocator zeroing: `PTPage::alloc` initializes fresh table pages itself.
  Using SVSM's actual page type also lets its native owner reclaim newly
  allocated child tables after a borrowed Verismo edit.
  The allocator is a zero-sized provider. Each operation reads SVSM's global
  root mapping, so controllers store no physical range, virtual base, or
  allocator ownership state. The host test checks mapping identity and
  allocation accounting.
- SVSM `phys_to_virt`/`virt_to_phys` and a small root-arena bounds accessor.
  The whole allocator arena is mapped privately in the new tree. Edits that
  overlap its virtual mapping are rejected, as are splits whose original huge
  leaf overlaps the arena even when the requested subpage does not.
- `SvsmPaging`'s private **and shared** masks, physical-address mask, and feature
  mask. Verismo applies that feature mask to requested mapping and leaf-update flags,
  including SVSM's early-boot `GLOBAL` suppression; the adapter does not repeat
  that filtering.
- SVSM's actual `TlbFlushScope`, range merge, and local/global/all-CPU flush
  implementations. Host tests replace instruction dispatch with an explicitly
  registered post-publication probe; production and in-guest builds
  retain native dispatch. Unexpected or CPU-local host callbacks fail the test
  rather than becoming silent no-ops.

The public wrapper passes `all_cpus=true`
to the core split, flag-update and range flag-update operations. There is
no CPU-local ownership guarantee for these SVSM mappings, including borrowed
roots, so the adapter never substitutes a local-only transition flush.

On x86, page-size transitions publish the initialized replacement subtree and
then synchronously flush before returning. When that flush covers the mutation,
its returned token is already discharged. Same-size edits can still return
deferred obligations. Handle any pending token before propagating a range error
or relying on changed permissions:

```rust,ignore
use verismo_paging::tlb::{MayNeedFlush, TlbFlush};

fn flush_pending<T: TlbFlush>(pending: MayNeedFlush<T>) {
    if pending.is_pending() {
        pending.flush_tlb_global_sync();
    }
}

flush_pending(table.split(va, PageLevel::Level0)?);
flush_pending(table.mprotect(va, PageLevel::Level0, PTEntryFlags::data_ro())?);
let (result, pending) = table.mprotect_range(region, PTEntryFlags::data_ro());
flush_pending(pending);
result?;
```

### Synchronous shootdown constraints

The production all-CPU path is
`TlbFlushScope::with_global(true).flush_all_cpus()`, not a local approximation.
In the pinned SVSM source:

- `kernel/src/cpu/tlb.rs::flush_all_cpus` selects the platform-wide callback
  once `FLUSH_SMP` is enabled. Its pre-SMP local branch is SVSM's existing boot
  lifecycle policy; the adapter does not change or independently reproduce it.
- The native/TDX default in `kernel/src/platform/mod.rs::flush_tlb` invokes
  `send_multicast_ipi(IpiTarget::All, ...)`. `kernel/src/cpu/ipi.rs::send_ipi`
  waits on the pending count with acquire ordering until remote handlers have
  completed. `TlbFlushScope::invoke` only performs the local TLB invalidation;
  it does not reenter this page-table controller or acquire its writer domain.
- The SNP override calls `kernel/src/sev/tlb.rs::flush_tlb_scope`; range and
  whole-ASID paths finish with `TLBSYNC` after `INVLPGB`.

The caller's writer exclusion must remain held through publication and
shootdown. No `LockSpec` is introduced for this sequential controller.
For IPI-based shootdowns, the caller must permit IPI delivery and execute at a
TPR no higher than `TPR_SYNCH`; the native sender asserts that requirement.
Do not use a writer-exclusion mechanism that disables required interrupts or
can be reentered by another interrupt/IPI handler that needs the same domain.
Code, stacks, direct-map pages and shootdown state needed during the callback
must remain accessible while the synchronous flush runs. Native panic or
failure to complete a shootdown is not converted to success or to a local flush.
These are live-kernel caller obligations, not properties established by host
tests or by a Rust `&mut` alone.

### Active-MMU reachability and the heap alias

SVSM's table-storage aliases are **not independent of its fixed heap mapping**.
`kernel/src/svsm.rs` installs the same heap virtual range into
`init_kernel_mapping_info` and `root_mem_init`. On the kernel target,
`kernel/src/mm/address_space.rs::phys_to_virt` returns that fixed alias;
`kernel/src/mm/pagetable.rs` uses it in `SvsmPaging::paddr_to_vaddr`. The bridge
likewise uses the arena's `start_virt` as its direct-map base. It does not create
an independent temporary mapping for table access. SVSM's recursive alias is
used by native address translation, not by the bridge's table-entry accesses,
and standard recursive roots remain unsupported imports.

The bridge rejects edits whose requested range directly overlaps the allocator
arena. Splitting an adjacent huge mapping is allowed because x86 publication
does not create a temporary hole: stale huge translations remain usable until
the synchronous flush completes, while new walkers can follow the published
child table. A native-tree regression exercises this neighboring split and
checks that the arena mapping remains usable. These checks do not detect whether
a borrowed tree is active, and no native boot consumer was migrated.

### Ownership and permission boundaries

The bridge uses `KernelPageTable` for its privileged native-root controller.
It propagates errors from the now-fallible unmap API. Creating a separate
`UserPageTable` with protected shared kernel entries is a different operation
from borrowing the existing SVSM root.

The Verismo dependency sets `default-features = false`. This disables
`concurrent`, selecting the sequential controller through `paging::pagetable`
(imported here under the `verismo_paging` dependency alias), while the absence
of `ignore_access_dirty_bits` retains atomic storage and preserves native
hardware-managed A/D history. Other consumers default to `concurrent`; there is
no separate concurrent module. Enabling `ignore_access_dirty_bits` permits
paging updates to discard A/D history. Entry storage remains atomic, and import
always preserves existing entry bits.

`unsafe { PageTable::from_svsm(&mut native_table) }` creates a lifetime-bound
controller using Verismo's `from_root` inside `ManuallyDrop`, without reclaiming
native pages. The wrapper releases the allocator through `leak` when the borrow
ends; owned trees instead use the controller's recursive destructor to reclaim
the root and all owned descendant table pages. No separate `free_children`
pass is needed. These table pages must be exclusively owned and allocated by
the same allocator; hardware users must be quiesced and external aliases
released before destruction. Mapped data frames remain externally owned.
The adapter's kernel controller owns all its table slots; user-policy shared
kernel slots, excluded from recursive reclamation by the core, are not used
by this wrapper. Native borrowed trees still suppress recursive destruction
through `ManuallyDrop`/`leak`, leaving root and descendants with their native owner.
The original native controller is unavailable until the borrow
ends. Other software aliases must also be excluded by the caller. Mapping
snapshots and unmap receipts use `PTEntry::leaf_address(level)` to decode frame
addresses without PAT bits.

Every flush obligation must be handled, including the obligation returned with
a range error. The host fixture calls `unsafe { flush.ignore() }` only because
its trees were never installed; synchronous transition probes instead require
an already-discharged token and never flush it again. `PROT_NONE` is rejected
(`InvalidFlags`), not silently translated into removal. Unknown flags, tagged physical inputs,
misalignment, unsupported levels, address overflow, and self-map edits are
rejected rather than truncated into different mappings.

No `PROT_NONE` requirement was found in the inspected SVSM consumers.
`ro_after_init::make_ro` requests present read-only mappings. SVSM's
`VMFileMapping::pt_flags` and `VMPhysMem::pt_flags` return **partial** flags;
`kernel/src/mm/vm/range.rs::map_vmm` explicitly adds `PRESENT`. A future caller
must perform that same composition before passing those partial flags to
`map` or `mprotect`; their absent `PRESENT` bit does not mean `PROT_NONE`.

SVSM's `paging/src/pagetable.rs::map_4k_with_parent_flags` applies parent flags to newly
allocated entries; `paging/src/ptpage.rs::alloc_pte_lvl*` leaves existing entries
unchanged. Implicitly widening imported ancestors would change that native
behavior. Protection remains a leaf-flag operation.

`tests.rs` runs inside the real kernel's existing host test harness with
`TestRootMem`. It exercises huge mapping/splitting, subpage read-only protection,
neighbor preservation, mapping an actual allocated payload page,
range protection and partial-error flushes, invalid operations, unmapping,
actual allocator exhaustion/rollback, self-map validation, and restoration of
allocator accounting after all root and child tables are released.
It additionally constructs an actual native SVSM `InstalledPageTable`, maps the
real allocator arena with SVSM's existing API, borrows it through Verismo, and
observes protection/unmapping changes through SVSM's native walker afterward.
Rejection of an unmapped root leaves native ownership intact; dropping a
successful borrow preserves the native root and children; native teardown then
reclaims both original and newly allocated table pages. Native PAT-bearing huge
entries exercise the split/PAT/A-D hooks, PAT-safe huge unmap receipts, and
preservation of inherited sibling flags. A standard recursive self-map is
explicitly rejected.

The transition probes capture real table-entry slots before entering an edit.
During the synchronous callback they require all-CPU/global scope and a
published child-table entry, matching x86 publish-then-flush ordering.
The probes cover explicit split, implicit protection, native borrowed
tables, 2 MiB range and 1 GiB full-scope transitions, allocation-failure retry,
and a range whose protected prefix survives a later gap. Exhaustion with only
one frame available also checks rollback of a partially prepared two-level split.
The existing same-size range-error case still checks its deferred flush.
No callback reenters the controller; it observes recorded slots atomically.
Unregistered callbacks also catch accidental flushes during construction,
idempotent splits or allocation failure before publication.

The payload-write helper is deliberately a **software permission check**, not a
CPU page-fault test. It checks writable flags, translation into the exact owned
`PageBox`, and private mapping status when confidentiality masks are nonzero
before writing through a bounded Rust slice. It only accepts owned trees with
Verismo-generated permissive ancestors, not borrowed trees whose ancestor flags
could impose additional restrictions. It never dereferences arbitrary test
physical addresses.

## Small host patch and remaining migration boundaries

Beyond adding the adapter/tests, the patch:

1. Exposes a read-only `root_memory_mapping` query beside SVSM's `root_mem_init`.
2. Registers the new kernel module and a local path dependency on Verismo.
3. Renames SVSM's **package** to `svsm-paging`, retaining the library name
   `paging` and the workspace dependency alias. This avoids Cargo's two local
   `paging 0.1.0` lockfile collision while preserving existing Rust imports/tests.
4. Aligns SVSM's optional Verus dependency pins with Verismo's
   `0.0.0-2026-08-02-0125`; Cargo otherwise rejects the incompatible exact
   prerelease pins even when SVSM verification features are disabled.
5. Adds 4 KiB geometry to SVSM's existing host and bare-metal compiler flags.

There is intentionally no fake installed-state conversion or borrowed-root
ownership trick:

- SVSM `kernel/src/mm/pagetable.rs` has `PageTable<Inactive/Installed>`,
  `allocate_inactive`, `clone_shared`, recursive `init_self_map`, and
  independently owned `PageTablePart` subtrees.
- Verismo `src/pagetable.rs::from_root` permits externally managed roots when
  their controller's Drop is suppressed with `ManuallyDrop`, as exercised
  here against actual SVSM tables. Its contract
  still requires an **acyclic**, self-mapped tree and no different-prefix
  aliases. SVSM's standard recursive root entry violates that contract, so
  `from_svsm` rejects the reserved recursive table slot before borrowing.
  Standalone PDPT subtrees also do not automatically contain the required
  allocator self-map. Suppressing Drop does not bypass these tree requirements.
- The native borrow only establishes exclusion through that particular Rust
  controller. SVSM `PerCpu::get_pgtable` and its shared subtrees require
  additional cross-controller exclusion. `make_ro_after_init` runs after
  `start_secondary_cpus` in `kernel/src/svsm.rs`; this fixture does not assume
  an exclusive Rust borrow alone supplies system-wide synchronization.
- Consequently existing SVSM boot, `PageTablePart`, and
  `make_region_ro_4k` consumers remain on their original implementation.
  This fixture proves the new API compiles and executes against real kernel
  services and compatible native-owned tables, not that the existing boot
  consumers have been migrated.
- `X86PagingParams` now supports shared masks and dynamic supported flags.
  This bridge retains `ArchPagingMeta` so its flush tokens contain the actual
  SVSM `TlbFlushScope`, without another token-conversion layer. Its x86
  split/PAT/A-D hooks are exercised against native SVSM entries.

Only native, unencrypted host execution was tested. SNP/TDX policies are
forwarded in code and compile for the kernel target, but encrypted hardware,
page-state transitions, SMP invalidation, active CR3 replacement, and SVSM Verus
proofs were **not** validated. The bare-metal binary may dead-strip this
unreferenced alternative API; its actual execution evidence is the host kernel
test, not a claim that the boot path runs it. Host transition probes establish
callback selection and publication ordering, not hardware TLB completion,
IPI liveness, or absence of interrupt-context deadlocks.
