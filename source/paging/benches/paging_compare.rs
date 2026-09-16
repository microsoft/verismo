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
use std::time::{Duration, Instant};

use common::{MemorySnapshot, Observation, PagingAdapter, HUGE_SIZE, PAGE_SIZE};
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
    Unmap,
    Walk,
    Protect,
    Split,
    ProtectRange,
    Mixed,
}

const WORKLOADS: [Workload; 9] = [
    Workload::MapMixed,
    Workload::MapLeafOnly,
    Workload::MapIntermediate,
    Workload::Unmap,
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
            Workload::Unmap => "unmap_4k",
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
}

/// Runtime benchmark settings and derived workload sizes.
struct Config {
    threads: Vec<usize>,
    base_work_per_thread: usize,
    items: WorkItems,
    range_pages: usize,
    warmups: usize,
    repetitions: usize,
}

#[derive(Clone, Copy)]
/// Per-thread item counts for each workload.
struct WorkItems {
    map_mixed: usize,
    map_leaf_only: usize,
    map_intermediate: usize,
    unmap: usize,
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
            Workload::Unmap => self.unmap,
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
            unmap: env_workload_items(
                "PAGING_BENCH_UNMAP_ITEMS_PER_THREAD",
                base_work_per_thread,
                4096,
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
        let config = Self {
            threads,
            base_work_per_thread,
            items,
            range_pages: env_usize("PAGING_BENCH_RANGE_PAGES", 16),
            warmups: env_usize("PAGING_BENCH_WARMUPS", 2),
            repetitions: env_usize("PAGING_BENCH_REPETITIONS", 9),
        };
        assert!(config.range_pages > 0);
        assert!(config.repetitions > 0);
        config
    }

    fn arena_pages(&self, workload: Workload, threads: usize) -> usize {
        let items = self.items.get(workload);
        let table_pages = match workload {
            Workload::MapIntermediate => threads.saturating_mul(items),
            Workload::Split => threads.saturating_mul(items),
            Workload::ProtectRange => {
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
        let range_span = config.items.protect_range as u64 * config.range_pages as u64 * PAGE_SIZE;
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
        let start = self.thread_base(thread) + item as u64 * self.range_pages as u64 * PAGE_SIZE;
        (start, start + self.range_pages as u64 * PAGE_SIZE)
    }

    fn frame(&self, virtual_address: u64) -> u64 {
        PHYSICAL_BASE + (virtual_address - VIRTUAL_BASE)
    }
}

/// Measurements and final state from one benchmark repetition.
struct Sample {
    elapsed: Duration,
    before: MemorySnapshot,
    after: MemorySnapshot,
    controller_inline: usize,
    controller_auxiliary: usize,
    fingerprint: u64,
}

/// All samples for one implementation, workload, and thread count.
struct Record {
    implementation: &'static str,
    workload: Workload,
    threads: usize,
    items_per_thread: usize,
    api_ops: usize,
    leaf_ops: usize,
    samples: Vec<Sample>,
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
        Workload::MapMixed | Workload::MapIntermediate => {}
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
            Workload::Unmap => adapter.unmap_4k(plan.point(thread, item)),
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
                Workload::Split => {
                    let base = plan.huge(thread, item);
                    for page in 0..512 {
                        let address = base + page * PAGE_SIZE;
                        let observation = adapter.observe(address);
                        assert_mapping(observation, plan.frame(address), PAGE_SIZE, true);
                        hash_observation(&mut fingerprint, observation);
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

fn run_once<A: PagingAdapter>(
    config: &Config,
    plan: &Plan,
    workload: Workload,
    threads: usize,
) -> Sample {
    let adapter = A::new(config.arena_pages(workload, threads));
    prepare(&adapter, workload, threads, plan);
    adapter.reset_peak();
    let before = adapter.memory();
    let ready = AtomicUsize::new(0);
    let go = AtomicBool::new(false);
    let elapsed = std::thread::scope(|scope| {
        let mut workers = Vec::with_capacity(threads);
        for thread in 0..threads {
            let adapter = &adapter;
            let plan = plan.clone();
            let ready = &ready;
            let go = &go;
            workers.push(scope.spawn(move || {
                ready.fetch_add(1, Ordering::Release);
                while !go.load(Ordering::Acquire) {
                    std::hint::spin_loop();
                }
                execute_thread(adapter, workload, thread, &plan);
                Instant::now()
            }));
        }
        while ready.load(Ordering::Acquire) != threads {
            std::hint::spin_loop();
        }
        let start = Instant::now();
        go.store(true, Ordering::Release);
        workers
            .into_iter()
            .map(|worker| worker.join().expect("benchmark worker"))
            .max()
            .expect("at least one worker")
            .duration_since(start)
    });
    let after = adapter.memory();
    let fingerprint = validate(&adapter, workload, threads, plan);
    let controller = adapter.controller_memory();
    Sample {
        elapsed,
        before,
        after,
        controller_inline: controller.inline_bytes,
        controller_auxiliary: controller.auxiliary_bytes,
        fingerprint,
    }
}

fn benchmark<A: PagingAdapter>(config: &Config, plan: &Plan, records: &mut Vec<Record>) {
    for workload in WORKLOADS {
        for &threads in &config.threads {
            for _ in 0..config.warmups {
                black_box(run_once::<A>(config, plan, workload, threads));
            }
            let samples = (0..config.repetitions)
                .map(|_| run_once::<A>(config, plan, workload, threads))
                .collect();
            let items_per_thread = plan.items(workload);
            let api_ops = threads * items_per_thread * workload.api_ops_per_item();
            let leaf_ops = match workload {
                Workload::ProtectRange => threads * items_per_thread * plan.range_pages,
                _ => api_ops,
            };
            records.push(Record {
                implementation: A::NAME,
                workload,
                threads,
                items_per_thread,
                api_ops,
                leaf_ops,
                samples,
            });
        }
    }
}

/// Three reported points from an ordered sample distribution.
struct Percentiles<T> {
    p10: T,
    median: T,
    p90: T,
}

fn interpolated_percentile(values: &[f64], percentile: f64) -> f64 {
    let position = (values.len() - 1) as f64 * percentile;
    let lower = position.floor() as usize;
    let upper = position.ceil() as usize;
    if lower == upper {
        values[lower]
    } else {
        let fraction = position - lower as f64;
        values[lower] + (values[upper] - values[lower]) * fraction
    }
}

fn percentiles_f64(mut values: Vec<f64>) -> Percentiles<f64> {
    assert!(!values.is_empty());
    values.sort_by(f64::total_cmp);
    Percentiles {
        p10: interpolated_percentile(&values, 0.1),
        median: interpolated_percentile(&values, 0.5),
        p90: interpolated_percentile(&values, 0.9),
    }
}

fn observed_percentile(values: &[usize], percentile: f64) -> usize {
    let index = ((values.len() - 1) as f64 * percentile).round() as usize;
    values[index]
}

fn percentiles_usize(mut values: Vec<usize>) -> Percentiles<usize> {
    assert!(!values.is_empty());
    values.sort_unstable();
    Percentiles {
        p10: observed_percentile(&values, 0.1),
        median: observed_percentile(&values, 0.5),
        p90: observed_percentile(&values, 0.9),
    }
}

fn throughput_median(record: &Record) -> f64 {
    percentiles_f64(
        record
            .samples
            .iter()
            .map(|sample| record.api_ops as f64 / sample.elapsed.as_secs_f64())
            .collect(),
    )
    .median
}

fn check_fingerprints(records: &[Record]) {
    let mut expected = BTreeMap::new();
    for record in records {
        let fingerprint = record.samples[0].fingerprint;
        assert!(record.samples.iter().all(|sample| sample.fingerprint == fingerprint));
        let key = (record.workload, record.threads);
        if let Some(other) = expected.insert(key, fingerprint) {
            assert_eq!(other, fingerprint, "cross-adapter fingerprint mismatch");
        }
    }
}

fn print_results(config: &Config, records: &[Record]) {
    println!(
        "configuration: threads={:?} base_work_per_thread={} range_pages={} warmups={} repetitions={}",
        config.threads,
        config.base_work_per_thread,
        config.range_pages,
        config.warmups,
        config.repetitions
    );
    println!(
        "effective_items_per_thread: map_mixed={} map_leaf_only={} map_intermediate={} unmap={} walk={} protect={} split={} protect_range={} mixed={}",
        config.items.map_mixed,
        config.items.map_leaf_only,
        config.items.map_intermediate,
        config.items.unmap,
        config.items.walk,
        config.items.protect,
        config.items.split,
        config.items.protect_range,
        config.items.mixed,
    );
    println!("TLB policy: synthetic tables only; all flush callbacks/receipts are no-ops");
    println!(
        "implementation,workload,threads,items_per_thread,api_ops,leaf_ops,ns/op[p10|median|p90],Mapi_ops/s[p10|median|p90],scaling,live_pages[before|p10|median|p90],peak_pages[p10|median|p90],live_bytes_median,peak_bytes_median,controller_bytes[inline|aux],fingerprint"
    );
    for record in records {
        let ns_per_op = percentiles_f64(
            record
                .samples
                .iter()
                .map(|sample| sample.elapsed.as_nanos() as f64 / record.api_ops as f64)
                .collect(),
        );
        let throughput = percentiles_f64(
            record
                .samples
                .iter()
                .map(|sample| record.api_ops as f64 / sample.elapsed.as_secs_f64() / 1_000_000.0)
                .collect(),
        );
        let live = percentiles_usize(
            record.samples.iter().map(|sample| sample.after.live_pages).collect(),
        );
        let peak = percentiles_usize(
            record.samples.iter().map(|sample| sample.after.peak_pages).collect(),
        );
        let base = records
            .iter()
            .find(|candidate| {
                candidate.implementation == record.implementation
                    && candidate.workload == record.workload
                    && candidate.threads == config.threads[0]
            })
            .unwrap();
        let scaling = throughput_median(record) / throughput_median(base);
        let sample = &record.samples[0];
        assert!(record
            .samples
            .iter()
            .all(|candidate| candidate.before.live_pages == sample.before.live_pages));
        assert!(record.samples.iter().all(|candidate| {
            candidate.controller_inline == sample.controller_inline
                && candidate.controller_auxiliary == sample.controller_auxiliary
        }));
        println!(
            "{},{},{},{},{},{},[{:.2}|{:.2}|{:.2}],[{:.3}|{:.3}|{:.3}],{:.2}x,[{}|{}|{}|{}],[{}|{}|{}],{},{},[{}|{}],{:016x}",
            record.implementation,
            record.workload.name(),
            record.threads,
            record.items_per_thread,
            record.api_ops,
            record.leaf_ops,
            ns_per_op.p10,
            ns_per_op.median,
            ns_per_op.p90,
            throughput.p10,
            throughput.median,
            throughput.p90,
            scaling,
            sample.before.live_pages,
            live.p10,
            live.median,
            live.p90,
            peak.p10,
            peak.median,
            peak.p90,
            live.median * PAGE_SIZE as usize,
            peak.median * PAGE_SIZE as usize,
            sample.controller_inline,
            sample.controller_auxiliary,
            sample.fingerprint,
        );
    }
}

fn main() {
    let config = Config::read();
    let plan = Plan::new(&config);
    let mut records = Vec::new();
    benchmark::<CurrentAdapter>(&config, &plan, &mut records);
    benchmark::<VeriosAdapter>(&config, &plan, &mut records);
    benchmark::<RustX86Adapter>(&config, &plan, &mut records);
    check_fingerprints(&records);
    print_results(&config, &records);
}
