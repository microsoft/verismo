# Paging comparison benchmark

`paging_compare` is a repository-owned adapter benchmark for:

- this checkout's concurrent `paging` controller;
- [`MSRSSP/verios-pagetable`](https://github.com/MSRSSP/verios-pagetable) at
  `b21b173cffbc9eae176dd8135f8b28121bd2d48c`;
- Rust `x86_64` crate `0.15.2`.

Run it on a host target. The first ordinary run stores Criterion's `base`
measurements under `target/criterion`; each later ordinary run compares with
the preceding measurements and then updates `base`:

```sh
CARGO_NET_GIT_FETCH_WITH_CLI=true \
  cargo bench -p verios-pagetable-beta --bench paging_compare \
  --target x86_64-unknown-linux-gnu
```

Save a named baseline when the reference measurements must not be replaced:

```sh
CARGO_NET_GIT_FETCH_WITH_CLI=true \
  cargo bench -p verios-pagetable-beta --bench paging_compare \
  --target x86_64-unknown-linux-gnu -- --save-baseline paging-main
```

Compare later measurements against that named baseline:

```sh
CARGO_NET_GIT_FETCH_WITH_CLI=true \
  cargo bench -p verios-pagetable-beta --bench paging_compare \
  --target x86_64-unknown-linux-gnu -- --baseline paging-main
```

Criterion owns warmup, sample collection, outlier analysis, persisted
measurements, and percentage-change reporting. Its CLI options, such as
`--warm-up-time`, `--measurement-time`, and `--sample-size`, control sampling.

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

The harness measures mixed-cost map, leaf-only map, map with intermediate-table
allocation, `map_region`, point unmap, `unmap_region`, walk/translate, protect,
2 MiB-to-4 KiB split, `protect_range`, and a mixed
read/protect/unmap/map sequence. The region workloads call paging's
`map_region`/`unmap_region` and VeriOS's `map_range`/`unmap_range` directly.
Their starts are offset from huge-page alignment so every adapter represents
the configurable range with matching 4 KiB leaves. Each
thread gets a disjoint address region and a fixed number of work items. Worker
threads announce readiness and spin on a shared start flag. Criterion excludes
adapter construction, workload setup, and worker creation through batched
setup; the measured routine releases the workers, performs the paging work,
and joins them. Benchmark paths include the workload, implementation, and
thread count. Throughput is reported in paging API operations. Range benchmark
names include the number of 4 KiB leaves affected by each range API operation.

All adapters use the same aligned, prefaulted arena design and the same
synthetic virtual addresses, frames, and permissions. Setup is outside the
timed interval. Before sampling each benchmark configuration, two untimed runs
must produce identical semantic fingerprints, live table-page counts, and
controller sizes; peak counts are checked against the live counts. Fingerprints
must also match across all three adapters. Final observations cover every
affected 4 KiB mapping, including all 512 leaves produced by each split.

The current and verios adapters use the same cache-line-isolated, arena-indexed
spin lock for each table page. The current adapter uses `X86Paging` and a
`DirectMappedAllocator`; the verios adapter uses its public
`PageTable<L4>`/`PtPageOps` surface and calls `pt_ops::split::split_l4`. The
`x86_64` adapter uses `MappedPageTable` behind one mutex because its mutation
API takes `&mut self`; its protect-range and split operations are implemented
locally with the crate's public page table representation. The split preserves
the benchmark's frame and flag semantics and clears the 2 MiB huge-page bit on
generated 4 KiB leaves.

No table is installed in CR3 and the benchmark executes no real TLB
instructions. Paging flush callbacks are no-ops, and flush receipts from
`paging` and `x86_64` are explicitly ignored. The numbers therefore compare
software page-table work only, not shootdown cost.

Environment variables:

- `PAGING_BENCH_THREADS` (default `1,2,4,8`)
- `PAGING_BENCH_WORK_PER_THREAD` (default `128`)
- `PAGING_BENCH_RANGE_PAGES` (default `16`, must be between `1` and `511`)

`PAGING_BENCH_WORK_PER_THREAD` is a base used to derive workload-specific
defaults. The default effective item counts per thread are:

- mixed-cost map: `base * 2048` (`262144`)
- leaf-only map: `base * 2048` (`262144`)
- map with intermediate allocation: `base * 4` (`512`)
- map region: `base * 256` (`32768` ranges)
- unmap: `base * 4096` (`524288`)
- unmap region: `base * 256` (`32768` ranges)
- walk/translate: `base * 8192` (`1048576`)
- protect: `base * 4096` (`524288`)
- split: `base * 4` (`512`)
- protect-range: `base * 256` (`32768` ranges)
- mixed: `base * 1024` (`131072` items, four API operations each)

Each effective count can be replaced directly with
`PAGING_BENCH_MAP_ITEMS_PER_THREAD`,
`PAGING_BENCH_MAP_LEAF_ONLY_ITEMS_PER_THREAD`,
`PAGING_BENCH_MAP_INTERMEDIATE_ITEMS_PER_THREAD`,
`PAGING_BENCH_MAP_RANGE_ITEMS_PER_THREAD`,
`PAGING_BENCH_UNMAP_ITEMS_PER_THREAD`,
`PAGING_BENCH_UNMAP_RANGE_ITEMS_PER_THREAD`,
`PAGING_BENCH_WALK_ITEMS_PER_THREAD`,
`PAGING_BENCH_PROTECT_ITEMS_PER_THREAD`,
`PAGING_BENCH_SPLIT_ITEMS_PER_THREAD`,
`PAGING_BENCH_PROTECT_RANGE_ITEMS_PER_THREAD`, or
`PAGING_BENCH_MIXED_ITEMS_PER_THREAD`. Split uses a much smaller multiplier
because every item creates a 4 KiB table and materializes 512 leaf entries.

Controller bytes are exact Rust logical sizes: inline adapter/controller state
plus the current adapter's owned stripe-domain/vector storage. Allocator
metadata and allocator implementation overhead are excluded. Peak page counts
include transient table allocations during the workload. These values are
correctness checks rather than a custom benchmark report.
