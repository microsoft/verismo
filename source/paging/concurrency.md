
## The two locking levels

Content locking is internal to the controller; callers provide no lock object
or protected-metadata type:

```rust
type Kernel = paging::pagetable::KernelPageTable<Arch, Alloc, Lvl<3>>;
let table = Kernel::new_empty()?;
```

The `PagingMutex<T>` alias selects ticket locking by default; `spin-mutex`
selects spin locking. Independently, `striped-locks` selects 64 static locks
instead of one global lock. Features are additive across consumers of the
same paging dependency.

Stripes hash the clean physical table-page number modulo 64. Shared pages
select the same lock regardless of the root or virtual direct-map address.
Collisions serialize unrelated pages; this is not true per-page locking.
Both modes lock individual updates, not whole walks or range operations.
Neither mutex disables interrupts: callers must prevent interrupt reentrancy.

`src/pagetable/` provides the `paging::pagetable` module. The crate has
no sequential controller or controller-selection feature.

`pagetable::PageTable<A, P, L, S = KernelPolicy>` separates tree
lifetime from content updates:

| Operation | Receiver | Content lock |
| --- | --- | --- |
| Walk, translate, inspect root entries | `&self` | None; atomic observations |
| Map, unmap, split, set flags, update encryption | `&self` | Page containing the entry being edited |
| `set_flags_range` | `&self` | Each table page while its affected entries are updated |
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

There is no public `walk_mut` returning a freely editable entry. `walk` returns
an owned `MappingSnapshot`; it is not a live reference, a whole-tree snapshot,
or a lifetime guarantee for a mapped data frame.

## Accessed and dirty bits

Hardware-updated A/D bits are preserved by default. The
`ignore_access_dirty_bits` feature permits software updates to discard those
bits. Entry storage is always atomic; private construction obtains ordinary
mutable access through `AtomicUsize::get_mut`.

| Features | Controller | Entry storage | A/D policy |
| --- | --- | --- | --- |
| Without `ignore_access_dirty_bits` | Concurrent | Atomic | Preserved |
| With `ignore_access_dirty_bits` | Concurrent | Atomic | Ignored |

`from_root`, `populate`, mapping, splitting and remapping preserve the entry
bits supplied by their callers. Paging never presets A/D or normalizes imported
trees. When A/D is preserved, valid-to-valid permission updates merge the latest
hardware A/D values into the replacement. Ignore mode makes no such guarantee.

`PTPagePointer` retains its raw pointer and lifetime-bound atomic access in every
mode. Sequential private construction may use ordinary page references because
its controller provides exclusive access; hardware access must still follow the
caller's paging and TLB protocol.

## Lifetime-bound page views

`src/structs/ptpage.rs` is a thin facade preserving the flat type paths.
Its implementation lives in `src/structs/ptpage/`: `node.rs` holds `PTPage`,
mapping types and entry-transition helpers; `node_pointer.rs` holds `PTPagePointer`,
`WalkResult`, entry access and traversal; and `tree.rs` holds the
`PTPageTree` owner, allocation, downward growth, release and tree-reclamation
helpers. References do not provide allocation or deallocation methods.
Host regressions live in `tests/*.rs` and exercise the public paging API.
Page sizes, level sizes and address-indexing helpers live together in
`src/structs/sizes.rs`, exported through `paging::structs`.

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

Walks use const-generic, monomorphized descent, while cleanup uses ordinary
recursion with a level-zero base case. The reference type needs neither `Copy`
nor `Clone`: operations borrow it. No level-dispatch macros or traversal enum
are needed. Root construction and raw entry access contain the pointer safety
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
The concurrent controller's private `map_or_alloc` allocates and initializes
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
Its level type `L: WalkLevel` has zero-sized
storage: the root level comes from `L::LEVEL`, with no runtime level field.
The controller retains no content-lock field or metadata marker. Its static
lock domain is independent of the tree's storage. The root and policy are not
duplicated.

Private preparations also use a statically leveled
`PTPageTree<A, P, L, KernelPolicy>`. Walk positions dispatch once to the
observed typed parent, then subtree growth and traversal recurse through
`PTPagePointer<L::ChildLevel>`. Boundary range edits retain a small staged-tree
enum because the live leaf level is observed at runtime; each variant owns a
typed tree. Mapping, unmapping, sweeping, validation, reclamation, teardown,
split construction, and split refresh all recurse through statically selected
child levels.

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
Walks and point-mutation attempts are bounded by the root depth plus one (at
most five). Each retry or newly published intermediate table makes the next
walk descend further; installed child links cannot be removed under a shared
borrow. Range flag updates allow two additional attempts because their leading
and trailing leaves may each require an independent split. Exhausting these
bounds is an invariant violation, not a recoverable mapping error.
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
split preparation retain ordinary writes, while live access uses the atomic
protocol. Existing unsafe raw-entry
accessors delegate to that protocol too, without fabricating a tree view when
no controller lifetime or page level is available.

Tree-layer reclamation uses these references and requires zero entry words
before reclaiming a table. Root ownership checks still exclude borrowed kernel
subtrees.

## Kernel and user policies

One implementation supports two ownership policies:

| Alias | Mutation authority | Reclamation |
| --- | --- | --- |
| `KernelPageTable<...>` | Privileged access throughout the tree | All owned descendants |
| `UserPageTable<...>` | Root slots selected by `OwnedIndices` | Only its owned descendants |

`PageTable` defaults to `KernelPolicy`. `new_from_sharing_top` takes a target
policy such as `UserPolicy<Owned>` and returns a table that owns the selected
`OwnedIndices` and borrows every other root entry. Borrowed entries are immutable
through the new controller, including slots that were empty when copied.
`UserPolicy<Owned>` is zero-sized: it contains no stored range or ownership bitmap.

Select one range with `CoveredRange<START, END>` or combine disjoint ranges with
`RootUnion<Left, Right>`. For example,
the following owns the lower half and borrows the upper half of a four-level root:

```rust,ignore
Table::new_from_sharing_top::<UserPolicy<CoveredRange<0, 256>>, _, _, _>(
    locks, &kernel, |table| table,
)
```

The reader closure may instead acquire a guard from a lock-protected source;
that guard is retained while copying and counting shares.
The selector works on root-slot indexes, not virtual addresses. With the
current 48-bit address type, the upper half occupies `511..512` in a five-level
root.

User tables can walk and translate kernel mappings. Map, unmap, flag updates,
split, and encryption updates reject kernel targets with
`PermissionDenied`. Range mutations check the complete requested range before
any update, so a forbidden kernel suffix cannot leave a modified user prefix.
Unmap methods return `Result` for both policies.
`set_flags_range` retains its error-plus-flush return shape.

Raw `populate` is unsafe and kernel-only; a user table never exposes an
unrestricted inner controller. New raw subtree attachments transfer ownership.
Staged raw edits must preserve valid, correctly leveled and exclusively owned
table links so later walks and destruction remain safe.
User cleanup skips the entire reserved kernel range, including when asked
to clean the entire tree, and leaves their root pointers intact.

The source borrow lasts only for construction; the returned table has no source
lifetime. Only a source policy implementing `MayShareSubtree` may lend entries.
When the source's `MAY_FREE_PAGE_TABLE_PAGES.frees_owned()` is true, the allocator's
`share_count` tracks borrowed root entries. Cleanup refuses shared entries, and
`Drop`/`free_children` panic before freeing still-shared owned entries. Otherwise
owned descendants are retained rather than freed. A borrower's `frees_shared()`
must match the source's `frees_owned()`; this is checked at compile time. Borrower
`Drop` and `release_shared` release tracked shares.

### Checked and ownership-unchecked mutations

The ordinary mutation methods retain their runtime ownership checks.
`map`, `map_with_parent_flags`, `unmap`, `split`, `set_flags`, `set_shared`,
`set_private`, `map_region`, `unmap_region`, and `set_flags_range` also have
unsafe `_unchecked` counterparts. These skip only the ownership-policy check;
the caller must establish that every affected root entry belongs to this
controller, rather than a borrowed subtree. Inclusive mapping ranges include
the final page in that obligation.

The unchecked cores retain structural validation, content locks, architecture
flag filtering, A/D handling, partial-failure semantics, and TLB obligations.
They do not grant permission to mutate a borrowed kernel mapping. Cleanup,
share-count checks, and shared-subtree lifetime requirements are unchanged.
These APIs prepare a boundary for future Verus preconditions; there are no
Verus contracts or proofs for them yet, and ordinary Rust callers must use
`unsafe` and justify the ownership obligation themselves.

Shared-access kernel updates remain available. Root pointers are copied, not
dynamically mirrored: initialize shared root slots before creating user roots
if subsequent kernel growth must be visible in those roots.

`leak` returns the raw root; `leak_with_policy` also returns
the user policy. Neither releases borrowed links or their share counts: raw
ownership transfers that obligation to the caller, without retaining a Rust
borrow of the source. Neither the policy nor share counts discharge hardware
quiescence or TLB obligations. Mapped data-frame ownership is still the embedder's
responsibility.

## Leaf flags, splitting and encryption

The page-table controller exposes these edit operations:

| Method | Effect |
| --- | --- |
| `split(vaddr, target, all_cpus)` | Refines a huge leaf to the requested level, preserving its mappings and attributes. Already-finer tables need no change. |
| `set_flags<PS>(page, flags, all_cpus)` | Changes the flags on exactly one typed page, splitting a larger leaf if necessary. |
| `set_flags_range(start, end, flags, all_cpus)` | Changes a smallest-page-aligned, half-open range, retaining large leaves when fully covered. |
| `set_shared(page, all_cpus)` / `set_private(page, all_cpus)` | Changes the selected typed page's encryption state, splitting a larger leaf if necessary. |

Edits return any remaining `MayNeedFlush` obligation. A live split completes its
architecture-selected transition protocol, so its returned token is already discharged.
Same-size flag and encryption updates can still require a later flush.
`all_cpus = true` selects `flush_tlb_global_sync`; `false` selects
`flush_tlb_global_percpu`. Both include global mappings. x86 publishes a fully
initialized split before flushing; architectures requiring break-before-make flush
after invalidation and before publication. Per-CPU mode requires no affected translations on another CPU and
no migration during the operation; it does not make an SMP shootdown local.
The same argument applies to `set_shared` and `set_private`.

Allocation failure while splitting does not change the original mapping.
`set_flags` refuses an already-finer subtree with `NotLeafEntry`, rather than replacing a
table pointer and stranding its children. The range helper recursively sweeps each covered
table and retains one page-keyed guard while updating consecutive entries in that table.
Each phase resolves a child once and processes the complete covered subrange below it
instead of restarting at the root for every leaf. After locking a table page, it
rereads each entry and checks whether the visited subrange covers the complete
leaf. A partial boundary leaf is split after releasing the guard, then the sweep
retries from that boundary. With no split, a flag update completes in one
hierarchical sweep.

Flag updates preserve the physical frame, confidentiality tag, PAT attribute,
page size, and accessed/dirty history. Other leaf flags are replaced.
Map and flag-update requests honor `ArchPagingMeta::supported_flags`;
unnamed extension bits are retained. Pure splitting preserves inherited
flags rather than reapplying the current feature policy.
Ancestor permissions still restrict effective access; this API does not
widen imported ancestor entries. Encryption updates retain the physical frame,
permissions, PAT and accessed/dirty history; they do not perform platform-specific
page-state conversion or cache maintenance.

Mapping initializes new parents but never widens existing ones. The default
parent flags permit leaf-level access control; callers choosing explicit parent
flags must allow the permissions their descendants will need. Imported trees
must already have suitable ancestor permissions. Leaf flag updates cannot override
an ancestor's missing USER/WRITABLE bits or its NX restriction.

For `set_flags` and `set_flags_range`, `flags` must include `PRESENT`;
clearing it returns `InvalidFlags`. This is a page-table edit API, not a
complete POSIX `mprotect` implementation: an embedder
must separately manage `PROT_NONE` policy, VMAs, and mapped data-frame lifetimes.
`set_flags` accepts only an aligned typed `Page<PS>`; `split` accepts any
address inside the selected mapping. Invalid ranges return `InvalidRange`.

Range edits are not transactions: lock-free readers may observe intermediate
states, and a missing mapping or allocation failure can leave a successful
prefix. Split preparation is all-or-nothing for each original huge leaf.
The error is returned **with any remaining** prefix flush obligation. Discharge
that obligation before propagating the error, for example:

```rust
use paging::{
    address::VirtAddr,
    pagetable::PageTable,
    structs::{ArchPagingMeta, PagingAllocator, PagingError, WalkLevel},
    tlb::MayNeedFlush,
};

fn update_flags<A, P, L>(
    table: &PageTable<A, P, L>,
    start: VirtAddr,
    end: VirtAddr,
    flags: A::PTFlags,
) -> Result<(), PagingError>
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevel,
{
    let (result, pending) = table.set_flags_range(start, end, flags, true);
    if pending.is_pending() {
        pending.flush_tlb_global_sync();
    }
    result
}
```

## Mutex-style content guards

The controller acquires a concrete spin-crate guard for a clean physical
table-page key. The guard releases its lock automatically; there is no
controller-specific production `Drop` implementation or test callback in
acquisition. Distinct keys may select the same lock because paging never
holds two content guards simultaneously.

A controller returned by `new_from_sharing_top` is not a writer of its
borrowed range. `UserPolicy` rejects edits there and excludes those root
entries from reclamation and Drop. Atomic entry reads permit concurrent updates
through the owner. Both controllers use the same static keyed lock domain.
The constructor remains unsafe because no source lifetime is retained and
raw ownership can bypass share-count accounting: callers must keep shared
descendants allocated while the returned controller or a leaked root can still
be used.

Range edits release the current page guard before acquiring a guard for another
table page. Consecutive leaves in one table therefore share one acquisition,
while disjoint stripes may be updated concurrently. A concurrent split can
change the observed walk shape after acquisition; the range update re-reads the
entry under the guard and retries descent through the published child.

Shared pages must also appear at identical virtual-address prefixes in every
root, so that a returned range flush covers each affected mapping. The host
must invalidate that range in every affected address space.

Allocation, unpublished-page reclamation and synchronous TLB hooks can run
under a content guard.
Allocation must return already accessible memory. These callbacks must not
re-enter the same content-lock domain or wait for software that needs the held
guard or exclusive access to this tree.

The optional `lock-wait-hook` feature uses a concrete `RelaxStrategy` inside
the selected mutex's wait loop. The embedder must define the
`extern "C" fn paging_lock_wait()` symbol and ensure that it returns normally,
does not allocate or acquire locks, and does not re-enter paging. Ticket
waiters retain their original queued ticket. A kernel may use this callback
to service only lock-independent TLB IPIs when IRQ masking would otherwise
block synchronous shootdown progress. Initialization, NMI safety, preemption
masking, and interrupt-priority guards remain the embedder's responsibility.

Focused concurrency regressions in `tests/concurrent.rs` check competing maps,
unmaps, path growth, and splits through the public API. Privileged register and
hardware translation tests remain in `tests/kvm`. Production acquisition and
guards have no test instrumentation.

Hardware installation is separate from `Live` tree access. The CPU-local
`ActivePageTable` and `RetiredPageTable` wrappers retain controllers rather than
freeing roots when dropped. A root switched out on one CPU is not detached or
globally quiesced. Recovering a retired controller requires explicit exclusion
of hardware users and invalidation of cached translations and page walks.
Raw CR3 reads/writes live in `arch/x86_64/regs.rs` (`paging::arch::x86_64`); managed
activation lives under `pagetable`. Neither disables interrupts or pins execution
to a CPU.

## Publication and update rules

`PTPage::alloc` obtains each fresh page through the provider's
`allocate_zeroed_table_page` contract before any entry is read or published.
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

A ranged update requiring splits changes at most two boundary-leaf paths. Each
boundary is split through the point-update protocol. x86 publishes one
replacement before synchronously flushing its old mapping. A BBM architecture
invalidates that structural entry, flushes, and then publishes its boundary
table. If both boundaries belong to one original huge leaf, the first split can
make the second boundary directly editable. No global allocator or unbounded
list of entries is needed.

Same-size flag updates retain compare-exchange retries to preserve hardware
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

Typed unmap removes the requested-size leaf under its lock, splitting a larger
leaf if needed and rejecting an already-finer subtree.
An entry returned by unmap is not ownership of its data frame: flush stale
translations and exclude outstanding data users before recycling that frame.
Use `old.leaf_address(target)` to decode the clean physical frame; the raw
`address()` field can still contain huge-page PAT.
Range operations do not provide whole-range snapshots or rollback on every
error. Flag updates exclude overlapping software writers one table page at a
time; other range helpers retain their documented per-entry behavior.

These are implementation contracts backed by host regression tests, not
formal verification of this concurrent implementation. `cargo verus focus`
continues to check the existing ghost modules separately.

Cleanup cannot be called through a shared tree borrow:

```compile_fail,E0596
use paging::{
    address::VirtAddr,
    pagetable::PageTable,
    structs::{ArchPagingMeta, PagingAllocator, WalkLevel},
    tlb::MayNeedFlush,
};

fn cleanup<A, P, L>(table: &PageTable<A, P, L>, addr: VirtAddr)
where
    A: ArchPagingMeta,
    P: PagingAllocator,
    L: WalkLevel,
{
    table.free_page_table_by_addr(addr, MayNeedFlush::none());
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
use paging::{
    address::VirtAddr,
    pagetable::UserPageTable,
    structs::{ArchPagingMeta, CoveredRange, PagingAllocator, RootComplement, WalkLevel},
};

fn raw_edit<A: ArchPagingMeta, P: PagingAllocator, L: WalkLevel>(
    user: &mut UserPageTable<A, P, L, RootComplement<CoveredRange<256, 512>>>,
    addr: VirtAddr,
) {
    let _ = user.walk_mut(addr);
}
```

Nor can it attach an unchecked subtree:

```compile_fail,E0308
use paging::{
    address::PhysAddr,
    pagetable::UserPageTable,
    structs::{ArchPagingMeta, CoveredRange, Lvl, PagingAllocator, RootComplement},
};

fn attach<A: ArchPagingMeta, P: PagingAllocator>(
    user: &mut UserPageTable<A, P, Lvl<3>, RootComplement<CoveredRange<256, 512>>>,
    child: PhysAddr,
) {
    let _ = user.populate_owned(0, child);
}
```

`new_from_sharing_top` and `populate_shared` are unsafe because the type system
does not retain the source owner. The caller must keep shared subtrees allocated
at the same virtual prefixes, use one atomic-access and content-lock protocol,
and unlink every sharing parent before synchronous TLB and page-walk
invalidation followed by reclamation.

Leaking a user table returns a raw root whose shared descendants are still
owned elsewhere. The caller must retain that owner until the leaked root is no
longer reachable.
