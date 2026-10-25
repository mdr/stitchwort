//! The counts must be the same on every run within a process, which they
//! aren't if the first run does one-time work (like building the standard
//! library's index) that later runs find done.
//!
//! In a file of its own because allocations are counted for the whole
//! process, so another test running at the same time would change them.

use stitchwort_bench::{programs, run};

#[test]
fn counts_repeat_within_a_process() {
    if cfg!(debug_assertions) {
        eprintln!("skipped: run in a release build (`cargo test --release`)");
        return;
    }
    // The slow tier repeats the whole example sweep: about 190 s, serial by
    // nature (allocations are counted per process). The fast tier repeats a
    // few small benchmarks, which catch one-time work the same way (the
    // first run builds whatever the later ones find done).
    let all = stitchwort_driver::driver::slow_tier_on();
    if !all {
        eprintln!("repeating a few small benchmarks only: slow tier off (`dev/t slow`)");
    }
    let chosen: Vec<_> = programs::ALL
        .iter()
        .filter(|b| {
            if all {
                b.name == "examples"
            } else {
                FAST.contains(&b.name)
            }
        })
        .collect();
    assert_eq!(
        chosen.len(),
        if all { 1 } else { FAST.len() },
        "benchmark names changed"
    );
    for benchmark in chosen {
        let outcome = run(benchmark, 2, false).expect("the benchmark runs");
        if let Some(variation) = outcome.variation {
            panic!(
                "{}'s counts differed between two runs in one process:\n{variation}",
                benchmark.name
            );
        }
    }
}

/// The benchmarks repeated outside the slow tier.
const FAST: &[&str] = &["eval-lengths", "run-prints", "check-long-sum"];
