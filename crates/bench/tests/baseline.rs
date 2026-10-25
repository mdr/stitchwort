//! The benchmarks' counts must not have regressed past the threshold
//! (docs/testing.md, "Benchmarks"). Counts are the same on every run, so this
//! can't fail by chance; times are left to `stitchwort-bench`, since they
//! could.
//!
//! Only in release builds (as `nix flake check` runs the tests): in a debug
//! build the benchmarks take minutes, and allocation counts can differ from
//! the release build's, which the baseline records.

use stitchwort_bench::baseline::{self, Baseline};
use stitchwort_bench::{Record, programs, run};

#[test]
fn counts_have_not_regressed() {
    if cfg!(debug_assertions) {
        eprintln!("skipped: run in a release build (`cargo test --release`)");
        return;
    }
    let baseline = Baseline::read(&baseline::default_path()).expect("a readable baseline");
    let mut records: Vec<(&str, Record)> = Vec::new();
    let mut failures = Vec::new();
    // The `examples` benchmark checks the whole example corpus on one thread
    // (allocations are counted per process): most of this test's time, so
    // only the full tier compares its counts.
    let whole_corpus = stitchwort_driver::driver::full_tier("the `examples` benchmark");
    for b in programs::ALL
        .iter()
        .filter(|b| whole_corpus || b.name != "examples")
    {
        match run(b, 1, false) {
            Ok(outcome) => records.push((b.name, outcome.record)),
            Err(e) => failures.push(format!("{} didn't run:\n{e}", b.name)),
        }
    }
    let results: Vec<(&str, &Record)> = records.iter().map(|(n, r)| (*n, r)).collect();
    let comparison = baseline::compare(&baseline, &results, false);
    println!("{comparison}");
    assert!(
        failures.is_empty() && !comparison.failed(),
        "{comparison}\n{}\nIf a regression is expected, record a new baseline with \
         `cargo run --release -p stitchwort-bench -- --update` and say why in the commit.",
        failures.join("\n")
    );
}
