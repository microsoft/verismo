# Paging comparison benchmark

`paging_compare` is a repository-owned adapter benchmark for:

- this checkout's concurrent `paging` controller;
- [`MSRSSP/verios-pagetable`](https://github.com/MSRSSP/verios-pagetable) at
  `b21b173cffbc9eae176dd8135f8b28121bd2d48c`;
- Rust `x86_64` crate `0.15.2`.

Run it on a host target:

```sh
CARGO_NET_GIT_FETCH_WITH_CLI=true \
  cargo bench -p paging --bench paging_compare \
  --target x86_64-unknown-linux-gnu
```

Check that optimized four-level translation retains straight-line page
descent:

```sh
./paging/benches/check_walk_codegen.sh
```

The check permits the two backward branches used for bounded revalidation
after concurrent table publication, but fails if page descent gains another
runtime loop.

The pinned verios repository must be reachable by the invoking Git
credentials.

The harness measures map, unmap, walk/translate, protect, 2 MiB-to-4 KiB
split, `protect_range`, and a mixed read/protect/unmap/map sequence. Each
thread gets a disjoint address region and a fixed number of work items. Worker
threads announce readiness and spin on a shared start flag. The coordinator
takes the start timestamp only after every worker is ready; elapsed time ends
at the latest worker completion timestamp, so thread creation, readiness, and
join teardown are excluded. Results report p10/median/p90 latency and
throughput, scaling relative to the smallest configured thread count, semantic
fingerprints, and exact allocator-instrumented live/peak table-page counts and
bytes for each implementation/workload. Floating-point latency and throughput
percentiles use linear interpolation over sorted samples; integer page counts
select the nearest observed sample.

All adapters use the same aligned, prefaulted arena design and the same
synthetic virtual addresses, frames, and permissions. Setup is outside the
timed interval. Final observations cover every affected 4 KiB mapping,
including all 512 leaves produced by each split.

The current adapter uses `X86Paging`, a `DirectMappedAllocator`, hashed content
mutexes, per-stripe reader counts, and a whole-domain writer gate implementing
`LockSpec` plus `LockAllSpec`. Reader counts are cache-line isolated, so
disjoint point operations do not contend on one shared reader word. The verios
adapter uses its public `PageTable<L4>`/`PtPageOps` surface and calls
`pt_ops::split::split_l4`. Its page locks are injective, as required by that
host contract. The `x86_64` adapter uses `MappedPageTable` behind one mutex
because its mutation API takes `&mut self`; its protect-range and split
operations are implemented locally with the crate's public page table
representation. The split preserves the benchmark's frame and flag semantics
and clears the 2 MiB huge-page bit on generated 4 KiB leaves.

No table is installed in CR3 and the benchmark executes no real TLB
instructions. Paging flush callbacks are no-ops, and flush receipts from
`paging` and `x86_64` are explicitly ignored. The numbers therefore compare
software page-table work only, not shootdown cost.

Environment variables:

- `PAGING_BENCH_THREADS` (default `1,2,4,8`)
- `PAGING_BENCH_WORK_PER_THREAD` (default `128`)
- `PAGING_BENCH_RANGE_PAGES` (default `16`)
- `PAGING_BENCH_WARMUPS` (default `2`)
- `PAGING_BENCH_REPETITIONS` (default `9`)
- `PAGING_BENCH_STRIPES` (default `256`)

`PAGING_BENCH_WORK_PER_THREAD` is a base used to derive workload-specific
defaults. The default effective item counts per thread are:

- map: `base * 2048` (`262144`)
- unmap: `base * 4096` (`524288`)
- walk/translate: `base * 8192` (`1048576`)
- protect: `base * 4096` (`524288`)
- split: `base * 4` (`512`)
- protect-range: `base * 256` (`32768` ranges)
- mixed: `base * 1024` (`131072` items, four API operations each)

Each effective count can be replaced directly with
`PAGING_BENCH_MAP_ITEMS_PER_THREAD`,
`PAGING_BENCH_UNMAP_ITEMS_PER_THREAD`,
`PAGING_BENCH_WALK_ITEMS_PER_THREAD`,
`PAGING_BENCH_PROTECT_ITEMS_PER_THREAD`,
`PAGING_BENCH_SPLIT_ITEMS_PER_THREAD`,
`PAGING_BENCH_PROTECT_RANGE_ITEMS_PER_THREAD`, or
`PAGING_BENCH_MIXED_ITEMS_PER_THREAD`. Split uses a much smaller multiplier
because every item creates a 4 KiB table and materializes 512 leaf entries.
The harness prints all effective counts before its CSV output.

Controller bytes are exact Rust logical sizes: inline adapter/controller state
plus the current adapter's owned stripe-domain/vector storage. Allocator
metadata and allocator implementation overhead are excluded. Peak page counts
include transient table allocations during the timed workload.
