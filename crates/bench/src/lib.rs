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
    /// The work to measure. Returns the steps and visits it took.
    pub run: Box<dyn FnOnce() -> Result<Work, String>>,
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
            run: Box::new(run),
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

/// One run of one benchmark.
pub struct Measurement {
    pub counts: Counts,
    pub inputs: Option<String>,
    pub time: Duration,
}

/// Runs `benchmark` once, on a thread of its own with [`STACK`] bytes of
/// stack.
pub fn measure(benchmark: &Benchmark) -> Result<Measurement, String> {
    with_stack(STACK, || {
        let prepared = (benchmark.prepare)()?;
        let before = alloc::start();
        let start = Instant::now();
        let work = (prepared.run)()?;
        let time = start.elapsed();
        let (allocations, peak_bytes) = alloc::since(before);
        Ok(Measurement {
            counts: Counts {
                steps: work.steps,
                visits: work.visits,
                allocations,
                peak_bytes,
            },
            inputs: prepared.inputs,
            time,
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
    /// Whether the counts differed between runs. They shouldn't.
    pub varied: bool,
}

/// Runs `benchmark` `runs` times (at least once), timing it if `timed`.
pub fn run(benchmark: &Benchmark, runs: usize, timed: bool) -> Result<Outcome, String> {
    let first = measure(benchmark)?;
    let mut times = vec![first.time];
    let mut varied = false;
    for _ in 1..runs.max(1) {
        let m = measure(benchmark)?;
        varied |= m.counts != first.counts;
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
        varied,
    })
}
