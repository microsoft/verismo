#[path = "paging_compare/common.rs"]
mod common;
#[path = "paging_compare/current.rs"]
mod current;
#[path = "paging_compare/rust_x86_64.rs"]
mod rust_x86_64;
#[path = "paging_compare/verios.rs"]
mod verios;

use std::collections::BTreeMap;
use std::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use common::{ControllerMemory, Observation, PagingAdapter, HUGE_SIZE, PAGE_SIZE};
use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion, Throughput};
use current::CurrentAdapter;
use rust_x86_64::RustX86Adapter;
use verios::VeriosAdapter;

const VIRTUAL_BASE: u64 = 0x0000_0010_0000_0000;
const PHYSICAL_BASE: u64 = 0x0000_0100_0000_0000;
const GIB: u64 = 1 << 30;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
/// One page-table operation measured by the harness.
enum Workload {
    MapMixed,
    MapLeafOnly,
    MapIntermediate,
    MapRange,
    Unmap,
    UnmapRange,
    Walk,
    Protect,
    Split,
    ProtectRange,
    Mixed,
}

const WORKLOADS: [Workload; 11] = [
    Workload::MapMixed,
    Workload::MapLeafOnly,
    Workload::MapIntermediate,
    Workload::MapRange,
    Workload::Unmap,
    Workload::UnmapRange,
    Workload::Walk,
    Workload::Protect,
    Workload::Split,
    Workload::ProtectRange,
    Workload::Mixed,
];

impl Workload {
    fn name(self) -> &'static str {
        match self {
            Workload::MapMixed => "map_mixed_4k",
            Workload::MapLeafOnly => "map_leaf_only_4k",
            Workload::MapIntermediate => "map_intermediate_4k",
            Workload::MapRange => "map_region",
            Workload::Unmap => "unmap_4k",
            Workload::UnmapRange => "unmap_region",
            Workload::Walk => "walk_translate",
            Workload::Protect => "protect_4k",
            Workload::Split => "split_2m_to_4k",
            Workload::ProtectRange => "protect_range",
            Workload::Mixed => "mixed",
        }
    }

    fn api_ops_per_item(self) -> usize {
        match self {
            Workload::Mixed => 4,
            _ => 1,
        }
    }

    fn criterion_name(self, range_pages: usize) -> String {
        match self {
            Workload::MapRange | Workload::UnmapRange | Workload::ProtectRange => {
                format!("{}_{}x4k_leaves", self.name(), range_pages)
            }
            _ => self.name().to_owned(),
        }
    }
}

/// Runtime benchmark settings and derived workload sizes.
struct Config {
    threads: Vec<usize>,
    items: WorkItems,
    range_pages: usize,
}

#[derive(Clone, Copy)]
/// Per-thread item counts for each workload.
struct WorkItems {
    map_mixed: usize,
    map_leaf_only: usize,
    map_intermediate: usize,
    map_range: usize,
    unmap: usize,
    unmap_range: usize,
    walk: usize,
    protect: usize,
    split: usize,
    protect_range: usize,
    mixed: usize,
}

impl WorkItems {
    fn get(self, workload: Workload) -> usize {
        match workload {
            Workload::MapMixed => self.map_mixed,
            Workload::MapLeafOnly => self.map_leaf_only,
            Workload::MapIntermediate => self.map_intermediate,
            Workload::MapRange => self.map_range,
            Workload::Unmap => self.unmap,
            Workload::UnmapRange => self.unmap_range,
            Workload::Walk => self.walk,
            Workload::Protect => self.protect,
            Workload::Split => self.split,
            Workload::ProtectRange => self.protect_range,
            Workload::Mixed => self.mixed,
        }
    }
}

impl Config {
    fn read() -> Self {
        let mut threads = env_list("PAGING_BENCH_THREADS", &[1, 2, 4, 8]);
        threads.sort_unstable();
        threads.dedup();
        assert!(!threads.is_empty() && threads.iter().all(|count| *count > 0));
        let base_work_per_thread = env_usize("PAGING_BENCH_WORK_PER_THREAD", 128);
        assert!(base_work_per_thread > 0);
        let items = WorkItems {
            map_mixed: env_workload_items(
                "PAGING_BENCH_MAP_ITEMS_PER_THREAD",
                base_work_per_thread,
                2048,
            ),
            map_leaf_only: env_workload_items(
                "PAGING_BENCH_MAP_LEAF_ONLY_ITEMS_PER_THREAD",
                base_work_per_thread,
                2048,
            ),
            map_intermediate: env_workload_items(
                "PAGING_BENCH_MAP_INTERMEDIATE_ITEMS_PER_THREAD",
                base_work_per_thread,
                4,
            ),
            map_range: env_workload_items(
                "PAGING_BENCH_MAP_RANGE_ITEMS_PER_THREAD",
                base_work_per_thread,
                256,
            ),
            unmap: env_workload_items(
                "PAGING_BENCH_UNMAP_ITEMS_PER_THREAD",
                base_work_per_thread,
                4096,
            ),
            unmap_range: env_workload_items(
                "PAGING_BENCH_UNMAP_RANGE_ITEMS_PER_THREAD",
                base_work_per_thread,
                256,
            ),
            walk: env_workload_items(
                "PAGING_BENCH_WALK_ITEMS_PER_THREAD",
                base_work_per_thread,
                8192,
            ),
            protect: env_workload_items(
                "PAGING_BENCH_PROTECT_ITEMS_PER_THREAD",
                base_work_per_thread,
                4096,
            ),
            split: env_workload_items(
                "PAGING_BENCH_SPLIT_ITEMS_PER_THREAD",
                base_work_per_thread,
                4,
            ),
            protect_range: env_workload_items(
                "PAGING_BENCH_PROTECT_RANGE_ITEMS_PER_THREAD",
                base_work_per_thread,
                256,
            ),
            mixed: env_workload_items(
                "PAGING_BENCH_MIXED_ITEMS_PER_THREAD",
                base_work_per_thread,
                1024,
            ),
        };
        let config =
            Self { threads, items, range_pages: env_usize("PAGING_BENCH_RANGE_PAGES", 16) };
        assert!(config.range_pages > 0 && config.range_pages < 512);
        config
    }

    fn arena_pages(&self, workload: Workload, threads: usize) -> usize {
        let items = self.items.get(workload);
        let table_pages = match workload {
            Workload::MapIntermediate => threads.saturating_mul(items),
            Workload::Split => threads.saturating_mul(items),
            Workload::MapRange | Workload::UnmapRange | Workload::ProtectRange => {
                threads.saturating_mul(items).saturating_mul(self.range_pages).div_ceil(512)
            }
            _ => threads.saturating_mul(items).div_ceil(512),
        };
        2048usize.saturating_add(2 * (table_pages + threads.saturating_mul(16)))
    }
}

#[derive(Clone)]
/// Shared address layout and workload plan.
struct Plan {
    items: WorkItems,
    range_pages: usize,
    stride: u64,
}

impl Plan {
    fn new(config: &Config) -> Self {
        let point_items = config
            .items
            .map_mixed
            .max(config.items.map_leaf_only)
            .max(config.items.unmap)
            .max(config.items.walk)
            .max(config.items.protect)
            .max(config.items.mixed);
        let point_span = point_items as u64 * PAGE_SIZE;
        let split_span = config.items.split as u64 * HUGE_SIZE;
        let intermediate_span = config.items.map_intermediate as u64 * HUGE_SIZE;
        let range_items =
            config.items.map_range.max(config.items.unmap_range).max(config.items.protect_range);
        let range_span = range_items as u64 * config.range_pages as u64 * PAGE_SIZE + PAGE_SIZE;
        let span = point_span.max(split_span).max(intermediate_span).max(range_span).max(GIB);
        let stride = span.div_ceil(GIB) * GIB;
        let max_thread = *config.threads.iter().max().unwrap() as u64;
        assert!(VIRTUAL_BASE + max_thread * stride < (1u64 << 47));
        assert!(PHYSICAL_BASE + max_thread * stride < (1u64 << 52));
        Self { items: config.items, range_pages: config.range_pages, stride }
    }

    fn items(&self, workload: Workload) -> usize {
        self.items.get(workload)
    }

    fn thread_base(&self, thread: usize) -> u64 {
        VIRTUAL_BASE + thread as u64 * self.stride
    }

    fn point(&self, thread: usize, item: usize) -> u64 {
        self.thread_base(thread) + item as u64 * PAGE_SIZE
    }

    fn huge(&self, thread: usize, item: usize) -> u64 {
        self.thread_base(thread) + item as u64 * HUGE_SIZE
    }

    fn intermediate(&self, thread: usize, item: usize) -> u64 {
        self.thread_base(thread) + item as u64 * HUGE_SIZE
    }

    fn range(&self, thread: usize, item: usize) -> (u64, u64) {
        let start = self.thread_base(thread)
            + PAGE_SIZE
            + item as u64 * self.range_pages as u64 * PAGE_SIZE;
        (start, start + self.range_pages as u64 * PAGE_SIZE)
    }

    fn frame(&self, virtual_address: u64) -> u64 {
        PHYSICAL_BASE + (virtual_address - VIRTUAL_BASE)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct CorrectnessResult {
    before_live_pages: usize,
    after_live_pages: usize,
    controller: ControllerMemory,
    fingerprint: u64,
}

struct PreparedRun<A: PagingAdapter> {
    adapter: Arc<A>,
    go: Arc<AtomicBool>,
    workers: Vec<std::thread::JoinHandle<()>>,
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).map_or(default, |value| value.parse().expect(name))
}

fn env_list(name: &str, default: &[usize]) -> Vec<usize> {
    std::env::var(name).map_or_else(
        |_| default.to_vec(),
        |value| value.split(',').map(|part| part.trim().parse().expect(name)).collect(),
    )
}

fn env_workload_items(name: &str, base: usize, multiplier: usize) -> usize {
    let default = base.checked_mul(multiplier).expect("workload item count overflow");
    let items = env_usize(name, default);
    assert!(items > 0, "{name} must be nonzero");
    items
}

fn prepare<A: PagingAdapter>(adapter: &A, workload: Workload, threads: usize, plan: &Plan) {
    let items = plan.items(workload);
    match workload {
        Workload::MapMixed | Workload::MapIntermediate | Workload::MapRange => {}
        Workload::MapLeafOnly => {
            for thread in 0..threads {
                for item in 0..items {
                    let address = plan.point(thread, item);
                    adapter.map_4k(address, plan.frame(address));
                    adapter.unmap_4k(address);
                }
            }
        }
        Workload::Unmap | Workload::Walk | Workload::Protect | Workload::Mixed => {
            for thread in 0..threads {
                for item in 0..items {
                    let virtual_address = plan.point(thread, item);
                    adapter.map_4k(virtual_address, plan.frame(virtual_address));
                }
            }
        }
        Workload::UnmapRange => {
            for thread in 0..threads {
                for item in 0..items {
                    let (start, end) = plan.range(thread, item);
                    adapter.map_range(start, end, plan.frame(start));
                }
            }
        }
        Workload::Split => {
            for thread in 0..threads {
                for item in 0..items {
                    let virtual_address = plan.huge(thread, item);
                    adapter.map_2m(virtual_address, plan.frame(virtual_address));
                }
            }
        }
        Workload::ProtectRange => {
            for thread in 0..threads {
                for item in 0..items {
                    let (start, end) = plan.range(thread, item);
                    let mut address = start;
                    while address < end {
                        adapter.map_4k(address, plan.frame(address));
                        address += PAGE_SIZE;
                    }
                }
            }
        }
    }
}

fn execute_thread<A: PagingAdapter>(adapter: &A, workload: Workload, thread: usize, plan: &Plan) {
    for item in 0..plan.items(workload) {
        match workload {
            Workload::MapMixed | Workload::MapLeafOnly => {
                let address = plan.point(thread, item);
                adapter.map_4k(address, plan.frame(address));
            }
            Workload::MapIntermediate => {
                let address = plan.intermediate(thread, item);
                adapter.map_4k(address, plan.frame(address));
            }
            Workload::MapRange => {
                let (start, end) = plan.range(thread, item);
                adapter.map_range(start, end, plan.frame(start));
            }
            Workload::Unmap => adapter.unmap_4k(plan.point(thread, item)),
            Workload::UnmapRange => {
                let (start, end) = plan.range(thread, item);
                adapter.unmap_range(start, end);
            }
            Workload::Walk => {
                black_box(adapter.translate(plan.point(thread, item)));
            }
            Workload::Protect => adapter.protect_4k(plan.point(thread, item), false),
            Workload::Split => adapter.split_2m_to_4k(plan.huge(thread, item)),
            Workload::ProtectRange => {
                let (start, end) = plan.range(thread, item);
                adapter.protect_range(start, end, false);
            }
            Workload::Mixed => {
                let address = plan.point(thread, item);
                black_box(adapter.observe(address));
                adapter.protect_4k(address, false);
                adapter.unmap_4k(address);
                adapter.map_4k(address, plan.frame(address));
            }
        }
    }
}

fn validate<A: PagingAdapter>(adapter: &A, workload: Workload, threads: usize, plan: &Plan) -> u64 {
    let mut fingerprint = 0xcbf2_9ce4_8422_2325u64;
    for thread in 0..threads {
        for item in 0..plan.items(workload) {
            match workload {
                Workload::Unmap => {
                    let observation = adapter.observe(plan.point(thread, item));
                    assert_eq!(observation, None);
                    hash_observation(&mut fingerprint, None);
                }
                Workload::UnmapRange => {
                    let (start, end) = plan.range(thread, item);
                    let mut address = start;
                    while address < end {
                        let observation = adapter.observe(address);
                        assert_eq!(observation, None);
                        hash_observation(&mut fingerprint, None);
                        address += PAGE_SIZE;
                    }
                }
                Workload::Split => {
                    let base = plan.huge(thread, item);
                    for page in 0..512 {
                        let address = base + page * PAGE_SIZE;
                        let observation = adapter.observe(address);
                        assert_mapping(observation, plan.frame(address), PAGE_SIZE, true);
                        hash_observation(&mut fingerprint, observation);
                    }
                }
                Workload::MapRange => {
                    let (start, end) = plan.range(thread, item);
                    let mut address = start;
                    while address < end {
                        let observation = adapter.observe(address);
                        assert_mapping(observation, plan.frame(address), PAGE_SIZE, true);
                        hash_observation(&mut fingerprint, observation);
                        address += PAGE_SIZE;
                    }
                }
                Workload::ProtectRange => {
                    let (start, end) = plan.range(thread, item);
                    let mut address = start;
                    while address < end {
                        let observation = adapter.observe(address);
                        assert_mapping(observation, plan.frame(address), PAGE_SIZE, false);
                        hash_observation(&mut fingerprint, observation);
                        address += PAGE_SIZE;
                    }
                }
                Workload::Protect => {
                    let address = plan.point(thread, item);
                    let observation = adapter.observe(address);
                    assert_mapping(observation, plan.frame(address), PAGE_SIZE, false);
                    hash_observation(&mut fingerprint, observation);
                }
                Workload::MapMixed | Workload::MapLeafOnly | Workload::Walk | Workload::Mixed => {
                    let address = plan.point(thread, item);
                    let observation = adapter.observe(address);
                    assert_mapping(observation, plan.frame(address), PAGE_SIZE, true);
                    hash_observation(&mut fingerprint, observation);
                }
                Workload::MapIntermediate => {
                    let address = plan.intermediate(thread, item);
                    let observation = adapter.observe(address);
                    assert_mapping(observation, plan.frame(address), PAGE_SIZE, true);
                    hash_observation(&mut fingerprint, observation);
                }
            }
        }
    }
    fingerprint
}

fn assert_mapping(observation: Option<Observation>, physical: u64, page_size: u64, writable: bool) {
    assert_eq!(
        observation,
        Some(Observation { physical, page_size, writable, user: true, executable: false })
    );
}

fn hash_observation(hash: &mut u64, observation: Option<Observation>) {
    let values = match observation {
        Some(value) => [
            1,
            value.physical,
            value.page_size,
            u64::from(value.writable),
            u64::from(value.user),
            u64::from(value.executable),
        ],
        None => [0, 0, 0, 0, 0, 0],
    };
    for value in values {
        *hash ^= value;
        *hash = hash.wrapping_mul(0x100_0000_01b3);
    }
}

fn prepare_run<A: PagingAdapter>(
    arena_pages: usize,
    plan: &Plan,
    workload: Workload,
    threads: usize,
) -> PreparedRun<A> {
    let adapter = Arc::new(A::new(arena_pages));
    prepare(&*adapter, workload, threads, plan);
    adapter.reset_peak();
    let ready = Arc::new(AtomicUsize::new(0));
    let go = Arc::new(AtomicBool::new(false));
    let mut workers = Vec::with_capacity(threads);
    for thread in 0..threads {
        let adapter = Arc::clone(&adapter);
        let plan = plan.clone();
        let ready = Arc::clone(&ready);
        let go = Arc::clone(&go);
        workers.push(std::thread::spawn(move || {
            ready.fetch_add(1, Ordering::Release);
            while !go.load(Ordering::Acquire) {
                std::hint::spin_loop();
            }
            execute_thread(&*adapter, workload, thread, &plan);
        }));
    }
    while ready.load(Ordering::Acquire) != threads {
        std::hint::spin_loop();
    }
    PreparedRun { adapter, go, workers }
}

impl<A: PagingAdapter> PreparedRun<A> {
    fn execute(self) -> Arc<A> {
        self.go.store(true, Ordering::Release);
        for worker in self.workers {
            worker.join().expect("benchmark worker");
        }
        self.adapter
    }
}

fn check_run<A: PagingAdapter>(
    config: &Config,
    plan: &Plan,
    workload: Workload,
    threads: usize,
) -> CorrectnessResult {
    let run = prepare_run::<A>(config.arena_pages(workload, threads), plan, workload, threads);
    let before = run.adapter.memory();
    assert_eq!(before.live_pages, before.peak_pages);
    let adapter = run.execute();
    let after = adapter.memory();
    assert!(after.peak_pages >= before.live_pages);
    assert!(after.peak_pages >= after.live_pages);
    CorrectnessResult {
        before_live_pages: before.live_pages,
        after_live_pages: after.live_pages,
        controller: adapter.controller_memory(),
        fingerprint: validate(&*adapter, workload, threads, plan),
    }
}

fn check_adapter<A: PagingAdapter>(
    config: &Config,
    plan: &Plan,
    fingerprints: &mut BTreeMap<(Workload, usize), u64>,
) {
    for workload in WORKLOADS {
        for &threads in &config.threads {
            let first = check_run::<A>(config, plan, workload, threads);
            let second = check_run::<A>(config, plan, workload, threads);
            assert_eq!(
                first,
                second,
                "{} {} {}-thread correctness result changed",
                A::NAME,
                workload.name(),
                threads
            );
            if let Some(expected) = fingerprints.insert((workload, threads), first.fingerprint) {
                assert_eq!(
                    expected,
                    first.fingerprint,
                    "{} {}-thread cross-adapter fingerprint mismatch",
                    workload.name(),
                    threads
                );
            }
        }
    }
}

fn register_adapter<A: PagingAdapter>(criterion: &mut Criterion, config: &Config, plan: &Plan) {
    for workload in WORKLOADS {
        let mut group = criterion.benchmark_group(workload.criterion_name(plan.range_pages));
        for &threads in &config.threads {
            let items_per_thread = plan.items(workload);
            let api_ops = threads
                .checked_mul(items_per_thread)
                .and_then(|items| items.checked_mul(workload.api_ops_per_item()))
                .expect("benchmark operation count overflow");
            group.throughput(Throughput::Elements(
                api_ops.try_into().expect("benchmark operation count exceeds u64"),
            ));
            let arena_pages = config.arena_pages(workload, threads);
            let benchmark_plan = plan.clone();
            group.bench_with_input(
                BenchmarkId::new(A::NAME, format!("{threads}t-{items_per_thread}items_per_thread")),
                &threads,
                move |bencher, &threads| {
                    bencher.iter_batched(
                        || prepare_run::<A>(arena_pages, &benchmark_plan, workload, threads),
                        PreparedRun::execute,
                        BatchSize::PerIteration,
                    );
                },
            );
        }
        group.finish();
    }
}

fn paging_compare(criterion: &mut Criterion) {
    let config = Config::read();
    let plan = Plan::new(&config);
    let mut fingerprints = BTreeMap::new();
    check_adapter::<CurrentAdapter>(&config, &plan, &mut fingerprints);
    check_adapter::<VeriosAdapter>(&config, &plan, &mut fingerprints);
    check_adapter::<RustX86Adapter>(&config, &plan, &mut fingerprints);
    register_adapter::<CurrentAdapter>(criterion, &config, &plan);
    register_adapter::<VeriosAdapter>(criterion, &config, &plan);
    register_adapter::<RustX86Adapter>(criterion, &config, &plan);
}

criterion_group!(benches, paging_compare);
criterion_main!(benches);
