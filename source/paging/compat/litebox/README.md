# LiteBox consumer integration

This is a feature-selectable replacement of the **real**
`litebox_platform_linux_kernel` x86 page-table backend, not a look-alike trait
fixture. It also builds into the real SNP runner. It is an integration experiment,
not a claim of a booted guest or production-ready SMP support.

Baseline: `microsoft/litebox`, commit
`8671b2439a78c789610acf3c7411eaac5fc3b312`.
The original local LiteBox worktree was clean and was not modified. All consumer
changes were made in an isolated local clone. Nothing was committed or uploaded.

## Retained files

- `backend.rs`: replacement backend, copied to the consumer's
  `litebox_platform_linux_kernel/src/arch/x86/mm/verismo.rs`.
- `backend_tests.rs`: thirteen additional tests compiled inside that actual platform.
- `litebox.patch`: consumer minimum-page configuration, optional
  dependency/feature, module selection, lockfile, native parent-creation/import
  fixes, and shared native/bridge test-fixture changes.
- `apply.py`: checks the exact baseline and a clean checkout before applying the
  portable patch and copying the two Rust files. No private absolute path is
  embedded in the retained patch.

The native backend remains selectable with the feature disabled and receives the
same parent-creation/import fix. The four original tests' assertions are unchanged.
Three additional shared tests exercise both backends. The mock fixture reserves a bounded 64-page
allocation pool and builds actual mappings for its registered physical-to-virtual
pages, including newly allocated page-table pages. It does **not** skip
`from_root` validation. Additional tests validate the table again after edits.

This adapter imports the existing boot root through `KernelPageTable` and
retains LiteBox's VMA checks. It does not create a new `UserPageTable` root.
Core unmap calls are fallible; the privileged controller
has unrestricted address authority, while user-policy controllers reject kernel
addresses with `PermissionDenied`.

The paging dependency retains its defaults, `use_ad` and `concurrent`.
`paging::pagetable` therefore provides the concurrent controller and lock traits;
there is no separate `pagetable_concurrent` module. Standard native comparisons
preserve hardware-managed accessed/dirty behavior. Active
borrowed boot roots require `use_ad` unless the caller can fully quiesce
hardware walkers, software access and all aliases to the table pages during
import, then invalidate paging-structure caches and TLBs on all affected CPUs
before resuming access. With `use_ad` disabled, `from_root` sets A/D on every
present parent and leaf after validation; newly installed present entries also
have A/D preset. `ManuallyDrop`/`leak` suppress reclamation, not normalization.
This adapter supplies no boot-import quiescence or cache-invalidation protocol,
and its content lock alone does not provide one. Do not disable dependency
defaults for an active boot root without establishing those obligations.

## Reproduce

Run from the Verismo repository root, setting paths appropriate to your machine:

```sh
export LITEBOX_SOURCE=/path/to/original/litebox
export LITEBOX_CHECKOUT=/path/to/isolated/litebox
export VERISMO_PAGING="$PWD/source/paging"
export ADAPTER="$VERISMO_PAGING/compat/litebox"
export CARGO_BUILD_JOBS=2

git clone --local "$LITEBOX_SOURCE" "$LITEBOX_CHECKOUT"
git -C "$LITEBOX_CHECKOUT" checkout --detach 8671b2439a78c789610acf3c7411eaac5fc3b312

(cd "$LITEBOX_CHECKOUT" &&
 cargo test -p litebox_platform_linux_kernel mm::tests -- --test-threads=1)

python3 "$ADAPTER/apply.py"
python3 "$ADAPTER/apply.py" --check-installed
cd "$LITEBOX_CHECKOUT"

cargo test --locked -p litebox_platform_linux_kernel \
  --features verismo-paging -- --test-threads=1

cargo check --locked -p litebox_platform_linux_kernel --features verismo-paging

cargo test --locked -p litebox_platform_linux_kernel \
  --no-default-features -- --test-threads=1

cargo +nightly-2025-12-31 build --locked \
  -Zbuild-std=core,compiler_builtins,alloc \
  -Zbuild-std-features=compiler-builtins-mem \
  --manifest-path=litebox_runner_snp/Cargo.toml \
  --target litebox_runner_snp/target.json \
  --features litebox_platform_linux_kernel/verismo-paging
```

The guest command is LiteBox's existing SNP build command with the backend
feature and paging's required minimum-page configuration added. Its toolchain
is the one pinned in `litebox_runner_snp/rust-toolchain.toml`.
The patch adds `.cargo/config.toml` with
`rustflags = ["--cfg", "target_min_page=\"4kib\""]`; this is a consumer selection,
not an additive Cargo feature or a default in the paging dependency. If your
environment overrides Cargo configuration using `RUSTFLAGS` or
`CARGO_ENCODED_RUSTFLAGS`, retain this selection in that override.

## Recorded validation

Latest targeted run (2026-09-16), after making boot-root adoption explicitly
unsafe at the public `LinuxKernel::new` boundary:
feature-enabled kernel-platform tests passed (20 tests), including the
non-`Clone` provider-marker and borrowed-root preservation regressions.

Host toolchain: `rustc 1.97.1 (8bab26f4f 2026-07-14)`,
`cargo 1.97.1 (c980f4866 2026-06-30)`.

| Command above | Result |
| --- | --- |
| Original kernel-platform `mm::tests` | 4 passed |
| Feature-enabled kernel-platform tests | 20 passed: 4 original, 3 new shared tests, 13 bridge tests |
| Non-test platform `cargo check` | Passed, including the privileged TLB callback implementation |
| Feature-disabled kernel-platform tests | 7 passed: 4 original and 3 new shared tests |
| Actual custom-target SNP runner build | Passed; statically linked x86-64 ELF at `target/target/debug/litebox_runner_snp` |
| `apply.py --check-installed` | Reverse patch check and retained-source byte comparisons passed |
| Non-destructive baseline validation | Temporary Git index loaded from the pinned commit; `git apply --cached --check --whitespace=error` passed without changing the worktree or its index |

The first bridge compilation correctly failed without `target_min_page`; adding
`--cfg target_min_page="4kib"` resolved it. Initial validation supplied it through
`RUSTFLAGS`; the retained patch now supplies the same selection through the
consumer's `.cargo/config.toml`, and both host tests and the guest build were
rerun without a `RUSTFLAGS` override. The first SNP build reported missing
`rust-src`; only then was
`rustup component add rust-src --toolchain nightly-2025-12-31` run. The selected
guest build also acquired its pinned toolchain through rustup. Formatting first
reported missing `rustfmt`; only then was its stable component installed.

Initial post-edit table validation caught a real fixture deficiency: the mock
allocator could expand outside its seeded mappings. Reserving the bounded pool
before building each mock root fixed that deficiency; the failing validation
assertions remain in the tests.

The added tests cover real `MemoryRegionPermissions`/`VmFlags` conversion,
`PROT_NONE`, preserved COW policy and explicit fault errors, actual allocated
frame preservation during VA relocation, huge-leaf splitting and neighbor
preservation, range protection and flush retention on partial failure,
VA relocation/collision handling, borrowed-root lifetime, and parallel edits
through LiteBox's actual spin locks. Permissions are also checked independently
through every ancestor, not just the returned leaf flags. The regressions cover
an initial RO/NX leaf followed by a writable/executable sibling, relocation into
a fresh subtree, rejection of missing USER/WRITE or inherited NX at each user
ancestor level, and preservation of restricted kernel subtrees. Anonymous data
zeroing is checked before relocation, and data contents are checked afterward.
Point and range split probes observe the initialized child table already
published inside the synchronous callback while the content mutex is held,
then require an empty returned token and preserved effective neighbor
permissions. Ordinary point protection and partial point-range failures still
require deferred flush tokens.

## Host interfaces and boundaries

- **Public contract:** `litebox/src/platform/page_mgmt.rs` and
  `litebox/src/mm/linux.rs` remain the sources of permissions, VMA ranges, and
  errors. The original `test_vmm_page_fault` still exercises the real
  `LiteBox -> PageManager -> LinuxKernel -> page table` path.
- **Allocation/layout:** the bridge uses the actual `MemoryProvider` and
  `PageTableAllocator` from `litebox_platform_linux_kernel/src/mm/{mod,pgtable}.rs`.
  The SNP provider supplies its high-half direct-map offset and bit-51 private
  mask in `src/host/snp/snp_impl.rs`; the noncontiguous host mock uses its actual
  registered address mapping. `Lvl<3>` matches LiteBox's four-level x86 backend.
  The allocator hook deliberately still uses `allocate_frame(true)`: fault
  handling also obtains anonymous data pages through that hook. Paging's own
  clearing of fresh table pages does not replace data-page zeroing.
  The zero-sized `Platform<M>` names a stateless global allocator and address
  mapping; no allocator value or ownership state is stored in a controller.
  Fault allocation and rollback call that same static provider.
- **Locking:** an outer `SpinMutex` preserves LiteBox's serialized multi-step
  operations. A separate shared spin lock implements `LockSpec<()>`; every page
  key acquires that mutex. The flush callback does not acquire the content
  guard. Host walks/faults participate in the outer lock. Snapshots are copied
  values, not pinned live entries or data frames.
- **TLB:** every affected paging call passes `FLUSH_ALL_CPUS = false`.
  Live x86 splits, including implicit protection splits and splits before VA relocation,
  publish the prepared subtree and synchronously invoke the per-CPU callback
  under the writer guard. The returned token is empty when this synchronous
  flush covered the edit. Point edits without
  a split still return deferred tokens, which the adapter discharges locally.
  Host tests record scopes instead of issuing privileged instructions.
  The guest implementation uses LiteBox's existing `x86_64` instruction
  dependency. Ranges through 2 MiB use `invlpg` at 4 KiB intervals; larger
  subtrees conservatively become full local flushes. Full flushes temporarily
  toggle CR4.PGE with interrupts disabled, restore every CR4 bit, and invalidate
  global and PCID-tagged translations without changing CR3/PCID. Merely calling
  the dependency's `flush_all` would reload CR3 and would not cover global
  translations. These privileged paths were compiled, not executed by host
  tests or a booted guest.
  LiteBox has no cross-CPU shootdown interface here: the synchronous callback
  explicitly fails if requested; it does not fall back to a local flush.
  This adapter requires the address space to remain pinned to one CPU for its
  entire active lifetime, with no migration or cached users on other CPUs.
  Merely having only one current runner is insufficient after migration.
  Software-thread concurrency tests do not establish multi-CPU TLB safety.
- **Borrowed boot root:** LiteBox's `PageTableImpl::init` does not transfer frame
  ownership. The bridge wraps paging's `from_root` result in `ManuallyDrop`,
  as required by that constructor's contract for externally managed roots.
  Its destructor releases the content lock through `leak`, without
  deallocating the root or any descendants. This suppression is essential:
  normal controller drop now recursively reclaims its policy-owned table pages,
  which must be exclusively owned and allocator-allocated, with hardware users
  quiesced and no outstanding external aliases. Borrowing the boot root does
  not establish those reclamation rights. Validation failure also leaves the root allocated.
  The boot owner must keep the tree
  and direct map alive. Imports require an acyclic, correctly leveled,
  self-mapped tree and exclusion of incompatible software walkers. The
  root-survival regression drops and readopts this actual borrowed controller.
- **Parent creation:** native fault and relocation paths, the Verismo bridge,
  and the mock boot-root builder use the shared `USER_PARENT_FLAGS` constant:
  `PRESENT|WRITABLE|USER|ACCESSED|DIRTY`, with NX clear. Both native mapping paths
  call `map_to_with_table_flags`; relocation no longer derives its ancestors
  from the first leaf's restrictive flags. The bridge only supplies these flags
  when allocating new ancestors. Leaf W/U/NX flags remain unchanged and determine
  the effective permissions. Neither mapping nor protection updates perform
  dynamic ancestor permission upgrades.
- **Actual boot/import path:** `litebox_runner_snp/src/main.rs` reads the current
  CR3 in `sandbox_process_init` and passes it to the unsafe
  `LinuxKernel::new`. The constructor's safety contract requires a page-aligned,
  accessible, correctly leveled, acyclic tree whose pages and direct mapping
  remain pinned, exclusion of incompatible software mutation, and the adapter's
  single-CPU lifetime constraint. This tree
  comes from the external SNP/Linux host, not a Rust boot-table builder in this
  checkout. Both implementations of `PageTableImpl::init` now call the shared,
  read-only `validate_user_parents` before constructing their controllers.
  Every present non-leaf entry in the lower half must already be writable,
  user-accessible and executable. A restrictive import panics with the table,
  slot and flags; it does not clear NX, widen USER/WRITE, rewrite descendants,
  change A/D history or flush an unchanged tree. Leaf restrictions, including
  supervisor-only and huge leaves, are retained. Upper-half kernel ancestors
  are exempt and untouched. The external boot producer must satisfy this
  explicit invariant; incompatible roots are not silently normalized.
- **User/kernel boundary:** safe platform allocation checks the declared task
  address bounds before fixed-address allocation or mapping. Both backends constrain range
  operations to the user half and reject kernel-address faults with
  `PageFaultError::AccessError`. Thus permissive user parents cannot be created
  inside a kernel subtree through these task-memory entry points.
- **Protection:** LiteBox implements `PROT_NONE` as present, supervisor-only,
  non-writable, NX. It therefore works with paging's present-only `set_flags`.
  Permission upgrades preserve LiteBox's deferred COW policy; the original
  unimplemented COW case now returns `PageFaultError::AccessError` rather than
  pretending the write succeeded. Execute-only conversion retains the original
  host limitation: user access is granted only when read or write is requested.
- **VA relocation:** LiteBox `remap_pages` moves virtual ranges using destination
  preflight and map-before-unmap under the host lock, preserving the source on a
  current-page allocation failure. It is not a whole-range transaction on OOM.
  Existing map/unmap/split operations implement this path; there is no
  physical-frame replacement API or replacement wrapper. Tests verify frame
  identity, data contents, collision handling and effective permissions.
- **Huge pages/errors:** the host VMA API still allocates 4 KiB data frames.
  Huge split/protect tests inspect real page-table storage but do not claim a
  huge-data-frame allocator or huge-VMA ownership scheme. Unexpected allocation
  errors splitting imported huge mappings cannot be represented by LiteBox's
  existing `PermissionUpdateError`; the bridge fails loudly instead of hiding
  them. Direct paging tests retain and discharge partial-range flushes.

No guest was booted. `/dev/kvm` was absent (`test -e /dev/kvm` returned 1), and
the SNP runner additionally needs its VMPL/sandbox-driver boot environment,
described by `src/host/snp/{wrapper.h,snp-sandbox.h}`. The ELF build and host tests
establish compilation and host-executed behavior only, not hardware translation,
IPI delivery, confidential-memory operation, or VM boot.
