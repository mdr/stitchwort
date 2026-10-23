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
    // About 95 s: serial by nature (allocations are counted per process).
    if !stitchwort_driver::driver::slow_tier("counts_repeat_within_a_process") {
        return;
    }
    let examples = programs::ALL.iter().find(|b| b.name == "examples").unwrap();
    let outcome = run(examples, 2, false).expect("the examples run");
    if let Some(variation) = outcome.variation {
        panic!("the examples' counts differed between two runs in one process:\n{variation}");
    }
}
