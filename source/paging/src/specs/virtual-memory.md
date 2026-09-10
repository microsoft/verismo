## There are 5 types of virtual address in OS.

| Type                          | VA → PA            | Mapping behavior                                                                                                |
| ----------------------------- | ------------------ | --------------------------------------------------------------------------------------------------------------- |
| **1. Direct/linear map**      | Page tables or `PA = VA - offset` | Deterministic arithmetic relationship                                                                           |
| **2. `vmalloc()`**            | Page tables        | VA range contiguous; each VA page gets a backing physical page; mapping normally stable while allocation exists |
| **3. Fixed/special mapping**  | Page tables        | Kernel explicitly maps VA to a particular physical/device range                                                 |
| **4. Recursive/self mapping** | Page tables        | VA is constructed to access a particular page-table level/page                                                  |
| **5. Demand-paged mapping**   | Page tables        | Physical backing can be established/replaced dynamically as VM events occur                                     |


Page table's virtual address may use Type 1, Type 3 or Type 4. Type-5 is usually used for userspace memory.




## How each type reaches physical memory

All five go through the page tables -- the MMU has no other mechanism. What
differs is *who decides the leaf entry*, and *whether it can be known or
predicted without reading it*.

```
            PHYSICAL MEMORY (4 KiB frames)
            ┌────┬────┬────┬────┬────┬────┬────┬────┬────┬────┐
            │ f0 │ f1 │ f2 │ f3 │ f4 │ f5 │ f6 │ f7 │ f8 │ f9 │
            └────┴────┴────┴────┴────┴────┴────┴────┴────┴────┘
```

Notation: `root`, `L3`, `L2`, `L1` are the table levels walked in order, and
`L1[i] = {pfn f}` is the leaf entry at index `i`, naming frame `f`.

### 1. Direct / linear map -- the leaf entry is forced by arithmetic

```
   VIRTUAL           PAGE-TABLE WALK                    PHYSICAL

   D+0x0000 ─► root ─► L3 ─► L2 ─► L1[0]   = {pfn 0}   ─►  PA 0x0000
   D+0x1000 ─► root ─► L3 ─► L2 ─► L1[1]   = {pfn 1}   ─►  PA 0x1000
   D+0x2000 ─► root ─► L3 ─► L2 ─► L1[2]   = {pfn 2}   ─►  PA 0x2000
   D+(n<<12) ─► root ─► L3 ─► L2 ─► L1[n]  = {pfn n}   ─►  PA n<<12

   invariant on the tables:  pfn == (VA - D) >> 12,  everywhere, forever
```

The walk still happens -- the arithmetic is an *invariant imposed on* the leaf
entries, established at boot and never broken. That is what lets a frame be
named without reading anything.

### 2. `vmalloc()` -- consecutive leaf entries, unrelated frames

```
   V+0x0000 ─► root ─► L3 ─► L2 ─► L1[0] = {pfn f5} ─►   f5
   V+0x1000 ─► root ─► L3 ─► L2 ─► L1[1] = {pfn f1} ─►   f1
   V+0x2000 ─► root ─► L3 ─► L2 ─► L1[2] = {pfn f9} ─►   f9
   V+0x3000 ─► root ─► L3 ─► L2 ─► L1[3] = {pfn f2} ─►   f2

   contiguous in VA (adjacent slots of one L1), arbitrary in PA
```

An object here spans many pages and therefore many frames: there is no single
frame number for the object.

### 3. Fixed / special mapping -- the leaf entry is chosen and remembered

```
   FIX_APIC ─► root ─► L3 ─► L2 ─► L1[k]   = {pfn 0xFEE00} ─►  device MMIO
   FIX_PT   ─► root ─► L3 ─► L2 ─► L1[k+1] = {pfn f6}      ─►  f6

   L1 here is statically allocated, so it is reachable before any mapping exists
```

Reachable only because someone wrote that entry, so the choice must be recorded
somewhere. It cannot bootstrap by itself: writing the entry is a PTE write,
which requires already reaching a table.

### 4. Recursive / self mapping -- the walk lands on the tables themselves

```
   root[S] = {pfn root}          the self entry: the root, as its own child

   VA = S│S│S│i4  ─► root[S]=root ─► root[S]=root ─► root[i4]={pfn T3} ─►  T3
                       (root as L3)     (root as L2)   (root as L1, leaf)

   VA = S│S│i4│i3 ─► root[S]=root ─► root[i4]=T3   ─► T3[i3]={pfn T2}  ─►  T2
                       (root as L3)     (T3 as L2)     (T3 as L1, leaf)

   VA = S│i4│i3│i2 ─► root[i4]=T3 ─► T3[i3]=T2     ─► T2[i2]={pfn T1}  ─►  T1
                       (T3 as L3)      (T2 as L2)     (T2 as L1, leaf)
```

Each walk stops one level early and reads a *table* entry as if it were a leaf,
so the frame it lands on is a page table. The VA is built from the walk path, so
it is knowable without a lookup -- but it is a function of the path, not of the
frame, so one shared table frame has one VA per path that reaches it, and a PTE
write changes which VAs exist.

### 5. Demand-paged mapping -- the leaf entry appears late, and may change

```
   before touch:  A+0x0000 ─► root  ─► L3  ─► L2  ─► L1[0]  = {not present} ──X fault
   after fault:   A+0x0000 ─► root  ─► L3  ─► L2  ─► L1[0]  = {pfn f7}      ─►  f7

   after fork:    A+0x0000 ─► root' ─► L3' ─► L2' ─► L1'[0] = {pfn f7, ro}  ─►  f7
                  the child is a second address space: same VA, same frame,
                  both sides marked read-only

   child writes:  A+0x0000 ─► root' ─► L3' ─► L2' ─► L1'[0] = {pfn f9, rw}  ─►  f9
                  only the faulting side is repointed; the parent keeps f7
```

The first state is not "a frame with unknown contents" -- there is *no frame at
all*, and the walk terminates in a fault. That is a distinct third state from
mapped-initialized and mapped-uninitialized.

Fork also shows the aliasing that matters most for permissions: between the fork
and the write, one frame is reachable from two address spaces at once, so a
permission naming only a virtual address is not enough to say what memory is
being written.

## How page tables use types 1, 3 and 4 to map page table pages

To write any PTE, the write itself must go through the MMU, so the table frame
needs a VA before it can be modified:

```
   write a leaf PTE for VA x
            │
            │ requires reaching the L1 table  ──┐
            │ requires reaching the L2 table    │  each of these frames
            │ requires reaching the L3 table    │  needs a VA of its own
            │ requires reaching the root table ─┘
            ▼
   ... which is itself a mapping, described by page tables
```

Types 1 and 4 break the regress because the address is a *total function* --
of the frame, or of the path -- so every table frame automatically has a VA.
Type 3 does not: it needs its own tables to be reachable already, so it can only
sit on top of a type 1 or type 4 core.
