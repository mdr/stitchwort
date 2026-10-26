//! `auto` proving membership in a long literal list stays fast: the proof is
//! a chain of cheap steps, not a search that grows with the list.

use std::process::Command;
use std::time::{Duration, Instant};

/// Checking a file whose `auto` argument is `n ∈ [1, …, length]`, with a
/// value that is in the list; the time it took.
fn check_membership(length: usize) -> Duration {
    let list: Vec<String> = (1..=length).map(|n| n.to_string()).collect();
    let source = format!(
        "import Std (List)\n\ndef probe (n: Nat) [auto ok: n ∈ [{}]]: Nat := n\n\ndef main: Nat := probe {length}\n",
        list.join(", ")
    );
    let dir = std::env::temp_dir().join(format!("stitchwort-membership-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(format!("membership{length}.sw"));
    std::fs::write(&path, source).expect("write source");
    let start = Instant::now();
    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
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

#[test]
fn membership_in_a_hundred_element_list_is_fast() {
    let elapsed = check_membership(100);
    assert!(
        elapsed < Duration::from_secs(5),
        "100 elements took {elapsed:?}"
    );
}

#[test]
fn membership_in_a_long_list_costs_little_more_than_in_a_short_one() {
    let short = check_membership(9);
    let long = check_membership(100);
    assert!(
        long < short * 5 + Duration::from_secs(1),
        "9 elements took {short:?}, 100 took {long:?}"
    );
}
