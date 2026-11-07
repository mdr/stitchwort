//! Recorded benchmarks (docs/testing.md, "Benchmarks").
//!
//! Each benchmark is measured in two ways:
//!
//! - **Counts**, the regression signal: evaluation steps (the resource
//!   budget's work counter), visits (levels of the recursive passes, like
//!   the elaborator and type checker, which aren't evaluation), heap
//!   allocations, and peak heap in use. They depend only on the program and
//!   the compiler, so they're the same on every run however busy the machine
//!   is, and a change in them is a change in the compiler. They don't see
//!   everything: a loop that neither evaluates, recurses through a guarded
//!   pass nor allocates costs time without changing them.
//! - **Time**, the median of several runs. It's what matters in the end, but
//!   other builds on the same machine make it noisy, so its threshold is
//!   loose and it's never checked automatically.
//!
//! Results are compared with `bench/baseline.toml` ([`baseline`]).

pub mod alloc;
pub mod baseline;
pub mod programs;

use std::time::{Duration, Instant};

use stitchwort_driver::driver::with_stack;

#[global_allocator]
static GLOBAL: alloc::Counting = alloc::Counting;

/// Benchmarks run with this much stack, and the matching resource limits:
/// the command line's.
pub const STACK: usize = 64 * 1024 * 1024;

pub struct Benchmark {
    pub name: &'static str,
    pub about: &'static str,
    /// Sets up the inputs, which isn't measured, and returns the work to
    /// measure.
    pub prepare: fn() -> Result<Prepared, String>,
}

/// A benchmark, ready to run.
pub struct Prepared {
    /// For inputs read from files that change as the project grows (like
    /// `examples/`): a fingerprint of them. Counts for other inputs aren't
    /// comparable.
    pub inputs: Option<String>,
    /// The names of the parts the work records counts for ([`Parts`]), in
    /// the order it records them: none for most benchmarks.
    pub parts: Vec<String>,
    /// The work to measure. Returns the steps and visits it took.
    pub run: Run,
}

/// The work a benchmark measures ([`Prepared::run`]).
pub type Run = Box<dyn FnOnce(&mut Parts) -> Result<Work, String>>;

/// What one part of a benchmark (one example file, say) counted: when a
/// benchmark's counts differ between runs, these say where.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PartCounts {
    pub steps: u64,
    pub visits: u64,
    pub allocations: u64,
    /// The most heap the part had in use at once, on its thread.
    pub peak_bytes: u64,
}

/// Where a benchmark's work records its parts' counts, in the order of
/// [`Prepared::parts`]. A benchmark with parts measures them on threads of
/// its own, so its totals are the parts' (see [`measure`]). Room for them
/// all is made before measuring starts, so recording them doesn't allocate.
pub struct Parts(Vec<PartCounts>);

impl Parts {
    /// Records the next part.
    pub fn record(&mut self, counts: PartCounts) {
        // Past the room made for them, recording would allocate: drop it.
        if self.0.len() < self.0.capacity() {
            self.0.push(counts);
        }
    }
}

/// What the resource budget counted: see [`Counts`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub steps: u64,
    pub visits: u64,
}

impl std::ops::Add for Work {
    type Output = Work;
    fn add(self, other: Work) -> Work {
        Work {
            steps: self.steps + other.steps,
            visits: self.visits + other.visits,
        }
    }
}

impl std::ops::Sub for Work {
    type Output = Work;
    fn sub(self, other: Work) -> Work {
        Work {
            steps: self.steps - other.steps,
            visits: self.visits - other.visits,
        }
    }
}

impl Prepared {
    pub fn new(run: impl FnOnce() -> Result<Work, String> + 'static) -> Prepared {
        Prepared {
            inputs: None,
            parts: Vec::new(),
            run: Box::new(move |_| run()),
        }
    }
}

/// The deterministic measures of one run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Counts {
    /// Evaluation steps (`Budget::total_work`).
    pub steps: u64,
    /// Levels of recursive passes (`Budget::total_visits`).
    pub visits: u64,
    pub allocations: u64,
    pub peak_bytes: u64,
}

impl Counts {
    fn named(&self) -> [(&'static str, u64); 4] {
        [
            ("steps", self.steps),
            ("visits", self.visits),
            ("allocations", self.allocations),
            ("peak bytes", self.peak_bytes),
        ]
    }
}

impl Counts {
    /// Whether `other` differs by no more than one part in 100,000 in any
    /// count. The parts of a benchmark spread over threads (`examples`) are
    /// not exactly the same on every run: a few examples, in 1,498, take a
    /// few dozen steps more or fewer, as if something in them depended on
    /// where the heap puts things, which another thread's allocations
    /// change. It is a millionth of the whole.
    fn close_to(&self, other: &Counts) -> bool {
        let near = |a: u64, b: u64| a.abs_diff(b) <= a.max(b) / 100_000;
        near(self.steps, other.steps)
            && near(self.visits, other.visits)
            && near(self.allocations, other.allocations)
            && near(self.peak_bytes, other.peak_bytes)
    }
}

impl PartCounts {
    fn named(&self) -> [(&'static str, u64); 4] {
        [
            ("steps", self.steps),
            ("visits", self.visits),
            ("allocations", self.allocations),
            ("peak bytes", self.peak_bytes),
        ]
    }
}

/// The counters that differ between `first` and `then`, with both values.
fn differences(first: &[(&'static str, u64)], then: &[(&'static str, u64)]) -> String {
    first
        .iter()
        .zip(then)
        .filter(|(a, b)| a.1 != b.1)
        .map(|((name, a), (_, b))| format!("{name} {a} then {b}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// One run of one benchmark.
pub struct Measurement {
    pub counts: Counts,
    pub inputs: Option<String>,
    pub time: Duration,
    /// Each part's name and counts ([`Prepared::parts`]).
    pub parts: Vec<(String, PartCounts)>,
}

/// Runs `benchmark` once, on a thread of its own with [`STACK`] bytes of
/// stack.
pub fn measure(benchmark: &Benchmark) -> Result<Measurement, String> {
    with_stack(STACK, || {
        let prepared = (benchmark.prepare)()?;
        let mut parts = Parts(Vec::with_capacity(prepared.parts.len()));
        let before = alloc::start();
        let start = Instant::now();
        let work = (prepared.run)(&mut parts);
        let time = start.elapsed();
        let (mut allocations, mut peak_bytes) = alloc::since(before);
        let work = work?;
        // Parts run on threads of their own: the benchmark's totals are
        // theirs, and its peak the heaviest part's, since the heap in use
        // overall would depend on how the threads interleave.
        if !parts.0.is_empty() {
            allocations = parts.0.iter().map(|p| p.allocations).sum();
            peak_bytes = parts.0.iter().map(|p| p.peak_bytes).max().unwrap_or(0);
        }
        Ok(Measurement {
            counts: Counts {
                steps: work.steps,
                visits: work.visits,
                allocations,
                peak_bytes,
            },
            inputs: prepared.inputs,
            time,
            parts: prepared.parts.into_iter().zip(parts.0).collect(),
        })
    })
}

/// What a benchmark measured over several runs.
#[derive(Clone, Debug, PartialEq)]
pub struct Record {
    /// From the first run.
    pub counts: Counts,
    pub inputs: Option<String>,
    /// The median, in milliseconds, if time was measured.
    pub time_ms: Option<f64>,
}

/// The result of running a benchmark `runs` times.
pub struct Outcome {
    pub record: Record,
    /// If the counts differed between runs, which they shouldn't: how.
    pub variation: Option<String>,
    /// Each part's counts from the first run ([`Prepared::parts`]).
    pub parts: Vec<(String, PartCounts)>,
}

/// Runs `benchmark` `runs` times (at least once), timing it if `timed`.
pub fn run(benchmark: &Benchmark, runs: usize, timed: bool) -> Result<Outcome, String> {
    let first = measure(benchmark)?;
    let mut times = vec![first.time];
    let mut variations = Vec::new();
    for run in 2..=runs.max(1) {
        let m = measure(benchmark)?;
        let same = if first.parts.is_empty() {
            m.counts == first.counts
        } else {
            m.counts.close_to(&first.counts)
        };
        if !same {
            variations.push(variation(&first, &m, run));
        }
        times.push(m.time);
    }
    times.sort();
    let median = times[times.len() / 2];
    Ok(Outcome {
        record: Record {
            counts: first.counts,
            inputs: first.inputs,
            time_ms: timed.then_some(median.as_secs_f64() * 1000.0),
        },
        variation: (!variations.is_empty()).then(|| variations.concat()),
        parts: first.parts,
    })
}

/// How run number `run`, `then`, differed from the first: its counters,
/// then its parts'.
fn variation(first: &Measurement, then: &Measurement, run: usize) -> String {
    let mut out = format!(
        "run {run} differed from run 1: {}\n",
        differences(&first.counts.named(), &then.counts.named())
    );
    for ((name, a), (_, b)) in first.parts.iter().zip(&then.parts) {
        if a != b {
            out += &format!("  {name}: {}\n", differences(&a.named(), &b.named()));
        }
    }
    if first.parts.len() != then.parts.len() {
        out += &format!(
            "  {} parts recorded, then {}\n",
            first.parts.len(),
            then.parts.len()
        );
    }
    out
}
