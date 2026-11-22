//! Proof step counts that can balloon without changing an answer, so that
//! only the hours-long all tier would notice until much later.
//!
//! `Aoc.Year2020.Day16.Proofs.runsNotes` took 55,437,062 evaluation steps on
//! 22 Nov 2026. Its ceiling is 65,000,000: a change that pushes it past that
//! is a slowdown to find, not a ceiling to raise without a reason.

use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The evaluation steps `check --timings=all` reports for `theorem` in `dir`.
fn steps(dir: &Path, namespace: &str, theorem: &str) -> u64 {
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .current_dir(dir)
        .args([
            "check",
            "--no-cache",
            "--timings=all",
            "--only",
            theorem,
            namespace,
        ])
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "check failed:\n{stderr}");
    let row = stderr
        .lines()
        .skip_while(|l| !l.starts_with("declaration "))
        .skip(1)
        .find(|l| l.starts_with(&format!("{theorem} ")))
        .unwrap_or_else(|| panic!("no declaration row for {theorem}:\n{stderr}"));
    // `name elab ms kernel ms total ms steps nodes read-back frames`.
    let words: Vec<&str> = row.split_whitespace().collect();
    words
        .get(words.len().saturating_sub(4))
        .and_then(|w| w.parse().ok())
        .unwrap_or_else(|| panic!("no step count in {row:?}"))
}

/// `Aoc.Year2020.Day16.Proofs.runsNotes` took 55,437,062 evaluation steps on
/// 22 Nov 2026. If this fails, find the change that made the proof take more
/// steps; do not raise the ceiling without a reason.
#[test]
fn aoc_day16_runs_notes_step_count_stays_under_its_ceiling() {
    const CEILING: u64 = 65_000_000;
    const NAMESPACE: &str = "Aoc.Year2020.Day16.Proofs";
    const THEOREM: &str = "Aoc.Year2020.Day16.Proofs.runsNotes";
    let measured = steps(&root().join("aoc"), NAMESPACE, THEOREM);
    assert!(
        measured <= CEILING,
        "{THEOREM} took {measured} steps, over its {CEILING} ceiling; \
         find the change that slowed it rather than raising the ceiling"
    );
}
