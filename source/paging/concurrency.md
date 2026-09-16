
## The two locking levels

The default `concurrent` Cargo feature selects `pagetable_concurrent.rs` as the
`paging::pagetable` module. Without it, that module selects the sequential
`pagetable.rs` implementation; the two implementations are not exposed together.

`pagetable::PageTable<A, P, L, K, T = (), S = KernelPolicy>` keeps the sequential
page-table API's allocation and TLB conventions, but separates tree lifetime
from content updates:

| Operation | Receiver | Content lock |
| --- | --- | --- |
| Walk, translate, inspect root entries | `&self` | None; atomic observations |
| Map, unmap, split, mprotect, update encryption | `&self` | Page containing the entry being edited |
| mprotect_range | `&self` | One second-level write guard excluding all content writers |
| Free empty tables or tear down children | `&mut self` | None; exclusive access required |
| Attach owned subtrees (kernel controllers only) | `&mut self`, unsafe | Root page |

An embedder can put the owner in its own `RwLock`: a read guard permits walks
and updates; a write guard permits cleanup. Rust borrowing excludes software
walkers during cleanup, but **does not exclude hardware walkers or users of
shared subtrees in another root**. Those are explicit unsafe obligations.
Discharge translation flushes and invalidate cached table pointers before
reusing reclaimed memory or resuming hardware walks.
Reclaimed pages must also have no parent links from another root: quiescing
that root's users does not remove its references. Shared subtrees are not
reference-counted; keep them allocated until all other parent links are gone.
Other controllers borrowing the same physical root must also be quiesced;
exclusive borrowing of one controller does not exclude those aliases.

Unlike the sequential implementation, there is no public `walk_mut` returning a
freely editable entry. `walk` returns an owned `MappingSnapshot`; it is not a
live reference, a whole-tree snapshot, or a lifetime guarantee for a mapped
data frame.

## Accessed and dirty bits

Both `use_ad` and `concurrent` are enabled by default. `PTPage` stores
`[AtomicUsize; ENTRY_COUNT]` whenever either feature is enabled; only disabling
both selects `[PTEntry<A>; ENTRY_COUNT]`.

| Features | Controller | Entry storage | A/D policy |
| --- | --- | --- | --- |
| Default: `use_ad`, `concurrent` | Concurrent | Atomic | Hardware maintained |
| Only `use_ad` | Sequential | Atomic | Hardware maintained |
| Only `concurrent` | Concurrent | Atomic | Software preset |
| Neither | Sequential | Plain | Software preset |

Disabling `use_ad` presets `ArchPagingMeta::accessed_dirty_mask()` on every
present entry constructed or published by paging. Both leaves and table pointers are covered. Raw
`PTEntry::from_bits` and reads remain exact; non-present words, including zero
entries, are not normalized.

Atomic stores, swaps, successful compare-exchanges and bitwise updates enforce
the disabled-mode policy. Bitwise updates use a compare-exchange loop in that
mode to enforce preset A/D only when the resulting entry is present.
Mapping, protection, splitting and encryption updates
retain the same publication and TLB protocols in both modes.

With `use_ad` disabled, `from_root` validates first, then presets A/D throughout
the imported tree, including shared pages. The caller must exclude all software
and hardware users, end conflicting Rust references through aliases, and
invalidate cached translations and paging-structure state before resuming use.
New raw subtrees passed to `populate` have the same normalization requirement.
Validation rejection does not normalize or adopt the tree.

`PTPagePointer` is unchanged: it retains its raw pointer and lifetime-bound atomic
access in both modes. Disabling hardware A/D updates does not eliminate concurrent
software writes, and an immutable reference to plain entries would forbid those
writes even under a content lock. Private construction and quiesced operations
can instead use ordinary page references; mutable entry references require
exclusive access with hardware excluded.

## Lifetime-bound page views

`src/structs/ptpage.rs` is a thin facade preserving the flat type paths.
Its implementation lives in `src/structs/ptpage/`: `node.rs` holds `PTPage`,
mapping types and entry-transition helpers; `node_pointer.rs` holds `PTPagePointer`,
`WalkResult`, entry access and traversal; and `tree.rs` holds the
`PTPageTree` owner, allocation, downward growth, release and tree-reclamation
helpers. References do not provide allocation or deallocation methods.
The x86_64 unit tests remain in `tests/unit/ptpage.rs`, included from `node.rs`
so storage fixtures can access private page fields.
Page sizes, level sizes and address-indexing helpers live together in
`src/structs/sizes.rs`, exported through `paging::sizes`.

Both implementations access live entries through an internal
`PTPagePointer<'tree, A, P>`. The reference stores a raw pointer and a runtime
`level: PageLevel`, never an ordinary reference to live `PTPage` storage. A
zero-sized lifetime and allocator marker retains the controlling tree borrow
and provider type. There is no cached physical address: `paddr()` uses the provider's
inverse address translation. Each controller constructs only a root view at
its `L::LEVEL`, tying `'tree` to its
tree-stabilizing borrow. Traversal derives child views from that root instead
of constructing views from arbitrary physical addresses.

`child(index)` atomically reads a checked slot. A present table pointer yields
a reference with the same tree lifetime at the next lower level. Huge,
absent and level-zero entries return their observed value rather than a child.

Walks and cleanup use ordinary recursion with a level-zero base case.
The reference type needs neither `Copy` nor `Clone`: operations borrow it. No level dispatch macros
or traversal enum are needed. Root construction and raw entry access contain the pointer safety
obligations, leaving walks and child traversal safe to call. Reclamation remains
explicitly unsafe because it requires external exclusion as well as valid
views. A walk returns a `WalkResult` containing only the stopping `PTPagePointer`
and entry index. Its `entry()` derives atomic access on demand; no entry value
or slot reference is cached. The node supplies the level and physical lock key
and permits further descent without reconstructing a reference from a raw address.
Concurrent snapshots load that entry explicitly and continue downward if it
has become a child table, returning only a leaf or absent-entry snapshot.

`walk(vaddr)` always finds a leaf or absent entry. Each sized mutation checks
the observed level before locking: a deeper entry means the requested slot
already contains a subtree, which the operation rejects or leaves unchanged.
The concurrent controller's private `walk_or_alloc` allocates and initializes
the complete missing path before locking. It then locks and rechecks the parent
slot, publishing the prepared subtree through one link only if the slot remains
absent. Losing preparations are reclaimed after unlocking; failed preparations
leave the live tree unchanged. The initial root walk happens once, before its
bounded allocation loop. If the locked recheck finds a child table, or after
publishing its own prepared child, the operation unlocks and continues walking
from the retained stopping node rather than restarting at the root. Installed
child links cannot be removed during this shared borrow, so each continuation
descends and the loop is bounded by the initial stopping depth plus one.
It returns an unlocked target slot, which mapping
locks and rechecks before publishing a leaf. Existing leaves above the target
and finer subtrees are never replaced by path allocation.

Both controllers contain a private `PTPageTree<A, P, L, S>` that stores the root
and ownership policy. Its allocator parameter names a stateless global provider.
Its level type `L: LevelSpec` has zero-sized
storage: the root level comes from `L::LEVEL`, with no runtime level field.
The concurrent controller additionally retains its content lock and metadata
marker. Neither controller duplicates the root or policy.

Private preparations use the same owner as `PTPageTree<A, P>`, defaulting to
`PageLevel` and `KernelPolicy`. Their runtime root level is needed because a
walk discovers the missing subtree's level dynamically. A small internal
`TreeLevel` trait selects zero-sized or runtime level storage; traversal still
uses runtime node references without type-dispatch macros.

The allocator is a stateless type-level provider backed by one global allocation
and address-translation domain. `new` allocates a zeroed root rather than accepting
a raw address. `grow` adds missing paths downward under an exclusive borrow,
and `Drop` frees the root and its owned descendant tables, not mapped data frames.
Consuming `release` uses `ManuallyDrop` and returns the root physical address
without freeing the pages. The provider's global domain must remain active;
publication callers already ensure that. This raw
release is restricted to wholly owned private preparations. Typed controllers
instead consume `into_parts`, retaining the ownership policy in user `leak`
results so shared kernel borrows are not lost.

Concurrent writers lock the page identified by that observation and reread the
entry. If another writer published a child before locking, they release the
guard and retry traversal. Allocation continues from its retained node; the
other mutation loops restart at the root. No content guard
is retained through descent. An absent observation is also reread under the
lock, since it may be a temporary invalidation during a page-size transition.
Walks and mutation attempts are bounded by the root depth plus one (at most
five). Each retry or newly published intermediate table makes the next walk
descend further; installed child links cannot be removed under a shared borrow.
Exhausting this bound is an invariant violation, not a recoverable mapping error.
This does not bound waiting inside the content lock or synchronous flush hooks.

Checked indexing also produces an internal entry view with atomic load, store,
swap and compare-exchange methods. Reads return copied `PTEntry` values.

Dropping a view does not unlink or free pages. Public mutable entry handles remain kernel-only,
and neither policy exposes a page view. Content locks still govern concurrent
writers; a mutable view alone does not authorize ordinary memory access.
Ordinary shared controller borrows pin installed table pages; reclamation needs
exclusive access. Cleanup derives the same level-aware views, ends child views
before freeing their unlinked pages, and retains the explicit hardware and
cross-controller exclusion obligations. Private construction and
split preparation retain ordinary writes, while sequential live access now uses
the same atomic protocol as concurrent access. Existing unsafe raw-entry
accessors delegate to that protocol too, without fabricating a tree view when
no controller lifetime or page level is available.

Tree-layer reclamation uses these references while retaining each controller's
emptiness predicate: sequential cleanup accepts non-present entries, whereas
concurrent cleanup requires zero words. Root ownership checks still exclude
borrowed kernel subtrees.

## Kernel and user policies

Both variants share one implementation across two controller types:

| Alias | Mutation authority | Reclamation |
| --- | --- | --- |
| `KernelPageTable<...>` | Privileged access throughout the tree | All owned descendants |
| `UserPageTable<'kernel, ...>` | Addresses outside the reserved kernel root slots | Only its owned descendants |

`PageTable` defaults to `KernelPolicy`. `new_from_sharing_top` is a kernel-only
constructor returning `UserPageTable`, not another privileged controller.
Its const-generic `START..END` range is immutable through the user controller,
including slots that were empty when copied. `UserPolicy<'kernel, START, END>`
is zero-sized: it contains only the kernel lifetime marker, with no stored range
or ownership bitmap. `owns_top_entry` is false for every reserved kernel slot.

Select the bounds when sharing, for example
`KernelPageTable::new_from_sharing_top::<256, 512>(&kernel)` for a
sequential four-level root's upper half; the concurrent constructor also takes
the content lock. The user aliases are `UserPageTable<'kernel, A, P, L, START, END>`
and `UserPageTable<'kernel, A, P, L, W, START, END, T = ()>`, respectively.
The bounds are root-slot indexes, not virtual addresses. With the current
48-bit address type, the upper half occupies `511..512` in a five-level root.

User tables can walk and translate kernel mappings. Map, unmap, protection,
split, and encryption updates reject kernel targets with
`PermissionDenied`. Range mutations check the complete requested range before
any update, so a forbidden kernel suffix cannot leave a modified user prefix.
Unmap methods return `Result` for both policies.
`mprotect_range` retains its error-plus-flush return shape.

Raw `populate` and sequential `walk_mut` are unsafe and kernel-only; a user table never
exposes an unrestricted inner controller. New raw subtree attachments transfer
ownership. Staged raw edits must preserve valid, correctly leveled and exclusively
owned table links so later walks and destruction remain safe.
User cleanup skips the entire reserved kernel range, including when asked
to clean the entire tree, and leaves their root pointers intact.

The source borrow keeps the kernel controller alive. Shared-access kernel
updates remain available in the concurrent variant, while exclusive kernel
operations wait for user-table borrows to end. Root pointers are copied, not
dynamically mirrored: initialize shared root slots before creating user roots
if subsequent kernel growth must be visible in those roots.

Kernel `leak` retains its original return shape. User `leak` also returns the
`UserPolicy` token; keep it while using the raw tree to retain the kernel borrow.
Neither the policy nor Rust borrowing discharges hardware quiescence or TLB
obligations. Mapped data-frame ownership is still the embedder's responsibility.

## Protection, splitting and encryption

Both page-table variants expose the same edit operations; the sequential
variant takes `&mut self` for all of them.

| Method | Effect |
| --- | --- |
| `split(vaddr, target, all_cpus)` | Refines a huge leaf to the requested level, preserving its mappings and attributes. Already-finer tables need no change. |
| `mprotect(vaddr, target, flags, all_cpus)` | Changes the flags on exactly one target-sized page, splitting a larger leaf if necessary. |
| `mprotect_range(start, end, flags, all_cpus)` | Changes a smallest-page-aligned, half-open range, retaining large leaves when fully covered. |
| `set_shared_4k(vaddr, all_cpus)` / `set_encrypted_4k(vaddr, all_cpus)` | Changes the selected smallest page's encryption state, splitting a larger leaf if necessary. |

Edits return any remaining `MayNeedFlush` obligation. A live split completes its
architecture-selected transition protocol, so its returned token is already discharged.
Same-size protection and encryption updates can still require a later flush.
`all_cpus = true` selects `flush_tlb_global_sync`; `false` selects
`flush_tlb_global_percpu`. Both include global mappings. x86 publishes a fully
initialized split before flushing; architectures requiring break-before-make flush
after invalidation and before publication. Per-CPU mode requires no affected translations on another CPU and
no migration during the operation; it does not make an SMP shootdown local.
The same argument applies to `set_shared_4k` and `set_encrypted_4k`.

Allocation failure while splitting does not change the original mapping.
`mprotect` refuses an already-finer subtree with `NotLeafEntry`, rather than replacing a
table pointer and stranding its children. The range helper recursively sweeps each covered
table under its second-level write guard. Each phase resolves a child once and processes
the complete covered subrange below it instead of restarting at the root for every leaf.
Two constant-cost boundary probes determine whether a partial huge leaf needs
preparation. With no split, protection completes in one hierarchical sweep.

Protection preserves the physical frame, confidentiality tag, PAT attribute,
page size, and accessed/dirty history. Other leaf flags are replaced.
Map and protection requests honor `ArchPagingMeta::supported_flags`;
unnamed extension bits are retained. Pure splitting preserves inherited
flags rather than reapplying the current feature policy.
Ancestor permissions still restrict effective access; this API does not
widen imported ancestor entries. Encryption updates retain the physical frame,
permissions, PAT and accessed/dirty history; they do not perform platform-specific
page-state conversion or cache maintenance.

Mapping initializes new parents but never widens existing ones. The default
parent flags permit leaf-level access control; callers choosing explicit parent
flags must allow the permissions their descendants will need. Imported trees
must already have suitable ancestor permissions. Leaf protection cannot override
an ancestor's missing USER/WRITABLE bits or its NX restriction.

For `mprotect` and `mprotect_range`, `flags` must include `PRESENT`;
clearing it returns `InvalidFlags`. This is a page-table edit API, not a
complete POSIX `mprotect` implementation: an embedder
must separately manage `PROT_NONE` policy, VMAs, and mapped data-frame lifetimes.
`mprotect` requires an address aligned to `target`; `split` accepts
any address inside the selected mapping. Invalid alignment and invalid ranges
return `InvalidAddress` and `InvalidRange`, respectively.

Range edits are not transactions: lock-free readers may observe intermediate
states, and a missing mapping or allocation failure can leave a successful
prefix. Split preparation is all-or-nothing for each original huge leaf.
The error is returned **with any remaining** prefix flush obligation. Discharge
that obligation before propagating the error, for example:

```rust
use paging::address::VirtAddr;
use paging::level::LevelSpec;
use paging::os_contract::{PagingError, PagingAllocator};
use paging::pagetable::{LockAllSpec, PageTable};
use paging::ArchPagingMeta;

fn protect<A, P, L, K>(
    table: &PageTable<A, P, L, K>,
    start: VirtAddr,
    end: VirtAddr,
    flags: A::PTFlags,
) -> Result<(), PagingError>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    K: LockAllSpec<()>,
{
    let (result, pending) = table.mprotect_range(start, end, flags, true);
    if pending.is_pending() {
        pending.flush_tlb_global_sync();
    }
    result
}
```

## Mutex-style content guards

`LockSpec<T>` follows Rust's `Mutex<T>` guard model. Its associated
`Guard<'a>` borrows the lock, implements `Deref<Target = T>` and `DerefMut`,
and releases the lock in `Drop`. There is no explicit `unlock`. Implementations
retain their own guard's thread-affinity restrictions.

The additional physical-page key selects lock granularity. A whole-tree
implementation ignores it; striped or per-page implementations use it to
choose a lock. Distinct keys may share a lock because the page-table code
never holds two content guards simultaneously. Every writer of a shared
physical table page must use the same exclusion domain.

`mprotect_range` additionally requires `LockAllSpec<T>`. Its `lock_all` guard
excludes **every** page-keyed writer and every other whole-domain writer until
drop, including writers through other roots sharing the domain. A whole-tree
mutex implements both acquisitions using that same mutex. A striped provider
needs a coordinated exclusion mechanism; locking one arbitrary stripe is not
sufficient. Range edits acquire this guard once and do not recursively acquire
page-keyed guards. Walks require neither guard.

Shared pages must also appear at identical virtual-address prefixes in every
root, so that a returned range flush covers each affected mapping. The host
must invalidate that range in every affected address space.

Allocation, unpublished-page reclamation and synchronous TLB hooks can run
under a content guard.
Allocation must return already accessible memory. These callbacks must not
re-enter the same content-lock domain or wait for software that needs the held
guard or exclusive access to this tree.

`T` is protected metadata or a permission object, not the live PTE array:
handing out `&mut` references to entries while atomic walkers access them
would violate Rust's aliasing rules. The current plain-Rust implementation
defaults to `T = ()`; it does not yet connect these guards to Verus tracked
permissions.

For example, a host implementation can wrap a standard mutex:

```rust
use paging::address::PhysAddr;
use paging::pagetable::{LockAllSpec, LockSpec};
use std::sync::{Mutex, MutexGuard};

struct WholeTreeLock<T>(Mutex<T>);

// SAFETY: every key uses the same mutex; its guard releases it on drop.
unsafe impl<T> LockSpec<T> for WholeTreeLock<T> {
    type Guard<'a> = MutexGuard<'a, T> where Self: 'a, T: 'a;

    fn lock(&self, _page: PhysAddr) -> Self::Guard<'_> {
        self.0.lock().expect("page-table content lock poisoned")
    }
}

// SAFETY: batch and page-keyed writers acquire the same mutex.
unsafe impl<T> LockAllSpec<T> for WholeTreeLock<T> {
    type AllGuard<'a> = MutexGuard<'a, T> where Self: 'a, T: 'a;

    fn lock_all(&self) -> Self::AllGuard<'_> {
        self.0.lock().expect("page-table content lock poisoned")
    }
}

let content = WholeTreeLock(Mutex::new(0usize));
{
    let mut guard = content.lock(PhysAddr::from(0usize));
    *guard += 1;
}
assert_eq!(*content.lock(PhysAddr::from(0usize)), 1);
```

## Publication and update rules

Allocators need not zero frames or initialize their contents. `PTPage::alloc`
clears each fresh page with ordinary writes before any entry is read or published.
Fresh construction, including its self-mapping checks, uses ordinary memory
accesses and does not acquire content locks. The same applies to off-tree
split children and newly allocated root entries copied from a shared tree.
Reading that shared source still requires atomic access.

Every live entry access is atomic. Walks use acquire loads; writers publish
initialized children with release stores. Writers re-read
an entry after locking, so a concurrent grow or split cannot be overwritten
using an earlier leaf observation.

An installed table pointer stays fixed until exclusive cleanup. A live split
prepares its private subtree and follows
`ArchPagingMeta::requires_break_before_make`. x86 atomically publishes the table
pointer and then completes the selected TLB flush. A baseline ARM implementation
must instead invalidate an unsafe valid-to-valid transition, complete its BBM
barrier, and then publish. The content write guard remains held throughout.
Children inherit the old mapping's attributes and hardware history, with the
requested edit applied only to selected leaves. New intermediate entries use
permissive parent flags.

An architecture using BBM must keep page-table access aliases, executing code,
stack and flush-handler state accessible while the entire old huge leaf is
temporarily absent. A content lock does not supply those mappings.

A ranged update requiring splits prepares at most two original boundary-leaf
subtrees. x86 publishes the replacements and updated interior leaves before one
synchronous flush. A BBM architecture invalidates only the structural boundary
entries, updates ordinary interior permissions, flushes once, and then publishes
the boundary tables. Both boundary paths may belong to one original huge leaf.
The flush covers the full old boundary mappings and uses the smallest original
leaf stride. No global allocator or unbounded list of entries is needed.

Same-size protection retains compare-exchange retries to preserve hardware
accessed/dirty changes. Removal uses atomic exchange;
single-bit encryption updates use atomic bitwise operations. Changing between two distinct
set-bit tags uses an invalidation barrier rather than exposing an intermediate
valid tag combination.

## Existing and borrowed roots

`from_root` imports an already initialized tree without clearing it and validates
self-mapping before constructing a controller. Rejection
or validation unwinding leaves the root allocated and releases the supplied
content-lock value normally.

Dropping either controller recursively frees its root and every owned descendant
table, never mapped data frames or reserved shared kernel subtrees. Explicit
`free_children` remains available and may precede Drop without double reclamation.
All reclaimed tables must be exclusively owned, allocator-allocated, and
quiesced, with no external parent links or hardware users. Drop does not acquire
content locks or perform TLB invalidation.

For an externally owned or still-active tree, wrap the result in `ManuallyDrop`
to suppress reclamation. `ManuallyDrop::into_inner(table).leak()` can release
the controller state
and lock value without deallocating any table pages; simply abandoning a
`ManuallyDrop` also skips those fields' destructors.

The constructor is unsafe: a raw physical address cannot establish a Rust
borrow of the original owner. The embedder must keep every linked page
accessible for the controller's lifetime and coordinate all other users.
New child pages still come from the global allocator provider. Cleanup may reclaim
only exclusively owned pages from that allocator, never foreign boot pages.
Suppressing Drop does not extend any allocation's lifetime or grant ownership
of foreign pages.

Sequential sharing remains unsafe. Its exclusion requirement covers the
**entire lifetime of mutable mapping handles**, including staged changes, not
merely the instant an entry is committed. Raw population transfers ownership
and cannot create another borrowed subtree behind the policy.

## Address and range limits

The existing `VirtAddr` type canonicalizes to 48 bits. A five-level root is
supported for addresses representable by that type; this module does not
extend the address type to the full 57-bit virtual-address space.

Split builds its entire requested path off-tree before publication. Allocation
failure leaves the original leaf intact. Ordinary map may instead leave
empty intermediate tables on failure; exclusive cleanup can reclaim them.

Unmap removes the leaf observed under its lock. If split wins first, unmap
removes the finer leaf subsequently found; it does not remove every child of
the former huge page. Exact-size unmap does nothing on a size mismatch.
An entry returned by unmap is not ownership of its data frame: flush stale
translations and exclude outstanding data users before recycling that frame.
Use `old.leaf_address(target)` to decode the clean physical frame; the raw
`address()` field can still contain huge-page PAT.
Range operations do not provide whole-range snapshots or rollback on every
error. Protection excludes overlapping software writers with its second-level
write guard; other range helpers retain their documented per-entry behavior.

These are implementation contracts backed by host regression tests, not
formal verification of this concurrent implementation. `cargo verus focus`
continues to check the existing ghost modules separately.

Cleanup cannot be called through a shared tree borrow:

```compile_fail,E0596
use paging::address::VirtAddr;
use paging::level::LevelSpec;
use paging::os_contract::PagingAllocator;
use paging::pagetable::{LockSpec, PageTable};
use paging::ArchPagingMeta;

fn cleanup<A, P, L, K>(table: &PageTable<A, P, L, K>, addr: VirtAddr)
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: LevelSpec,
    K: LockSpec<()>,
{
    unsafe { table.free_page_table_by_addr(addr) };
}
```

## Target configuration

Consumers building outside this workspace must select the page geometry in
their own Cargo configuration, for example `rustflags = ["--cfg",
'target_min_page="4kib"']` under `[build]`. Rustdoc needs the same setting in
`rustdocflags`. This is intentionally target configuration, not an additive
Cargo feature that another dependency could silently change.

## Static policy boundaries

A user controller cannot expose a mutable raw entry:

```compile_fail,E0599
use paging::address::VirtAddr;
use paging::level::LevelSpec;
use paging::os_contract::PagingAllocator;
use paging::pagetable::{LockSpec, UserPageTable};
use paging::ArchPagingMeta;

fn raw_edit<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, K: LockSpec<()>>(
    user: &mut UserPageTable<'_, A, P, L, K, 256, 512>,
    addr: VirtAddr,
) {
    let _ = user.walk_mut(addr);
}
```

Nor can it attach an unchecked subtree:

```compile_fail,E0599
use paging::address::PhysAddr;
use paging::level::LevelSpec;
use paging::os_contract::PagingAllocator;
use paging::pagetable::{LockSpec, UserPageTable};
use paging::ArchPagingMeta;

fn attach<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, K: LockSpec<()>>(
    user: &mut UserPageTable<'_, A, P, L, K, 256, 512>,
    child: PhysAddr,
) {
    let _ = unsafe { user.populate(0, child) };
}
```

The kernel owner cannot be dropped before its user controller:

```compile_fail,E0505
use paging::level::LevelSpec;
use paging::os_contract::PagingAllocator;
use paging::pagetable::{KernelPageTable, LockSpec};
use paging::ArchPagingMeta;

fn retire<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, W: LockSpec<()>>(
    kernel: KernelPageTable<A, P, L, W>,
    wperms: W,
) {
    let user = unsafe {
        KernelPageTable::new_from_sharing_top::<256, 512>(wperms, &kernel)
    }.unwrap();
    drop(kernel);
    drop(user);
}
```

Returning raw user-tree parts does not erase that borrow:

```compile_fail,E0505
use paging::level::LevelSpec;
use paging::os_contract::PagingAllocator;
use paging::pagetable::{KernelPageTable, LockSpec};
use paging::ArchPagingMeta;

fn leak_user<A: ArchPagingMeta, P: PagingAllocator, L: LevelSpec, W: LockSpec<()>>(
    kernel: KernelPageTable<A, P, L, W>,
    wperms: W,
) {
    let user = unsafe {
        KernelPageTable::new_from_sharing_top::<256, 512>(wperms, &kernel)
    }.unwrap();
    let (_wperms, policy, _root) = user.leak();
    drop(kernel);
    drop(policy);
}
```
