//! `auto` proving membership in a long literal list stays fast: the proof is
//! a chain of cheap steps, not a search that grows with the list.

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

/// Checking a file in `dir` whose `auto` argument is `n ∈ [1, …, length]`,
/// with a value that is in the list; the time it took. The library comes
/// from a check cache in `dir`, so only the first run checks it.
fn check_membership(dir: &Path, length: usize) -> Duration {
    let list: Vec<String> = (1..=length).map(|n| n.to_string()).collect();
    let source = format!(
        "import Std (List)\n\ndef probe (n: Nat) [auto ok: n ∈ [{}]]: Nat := n\n\ndef main: Nat := probe {length}\n",
        list.join(", ")
    );
    let path = dir.join(format!("membership{length}.sw"));
    std::fs::write(&path, source).expect("write source");
    let start = Instant::now();
    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("check")
        .arg("--cache-dir")
        .arg(dir.join("cache"))
        .arg(&path)
        .output()
        .expect("run stitchwort");
    let elapsed = start.elapsed();
    assert!(
        out.status.success(),
        "{length} elements failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    elapsed
}

/// Times are only compared with each other: the fastest of three
/// alternating runs of each size, so a busy machine slows both alike. Every
/// check pays the same start-up, so the ratio is near 1 unless the proof's
/// cost grows quickly with the list's length.
#[test]
fn membership_in_a_long_list_costs_little_more_than_in_a_short_one() {
    let dir = std::env::temp_dir().join(format!("stitchwort-membership-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let (mut short, mut long) = (Duration::MAX, Duration::MAX);
    for _ in 0..3 {
        short = short.min(check_membership(&dir, 9));
        long = long.min(check_membership(&dir, 100));
    }
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        long < short * 3,
        "9 elements took {short:?}, 100 took {long:?}"
    );
}
