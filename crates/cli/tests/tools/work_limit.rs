//! `STITCHWORT_WORK_LIMIT`: the per-declaration evaluation-step limit, lowered
//! for tests and debugging (crates/core/src/budget.rs).

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// A file whose theorem computes for real: `countBig` takes 1.6 million
/// evaluation steps.
fn source() -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("work-limit");
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    let path = dir.join("work-limit.sw");
    std::fs::write(
        &path,
        "import Std (Eq, Nat)\n\n\
         def count: Nat -> Nat\n  \
         | Zero => Zero\n  \
         | Succ n => Succ (count n)\n\n\
         theorem countBig: count 100000 = 100000 := byComputing\n",
    )
    .expect("write source");
    path
}

/// Checks `path` with `STITCHWORT_WORK_LIMIT` set to `limit`, or removed.
fn check(path: &Path, limit: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.args(["check", "--no-cache"]).arg(path);
    match limit {
        Some(limit) => command.env("STITCHWORT_WORK_LIMIT", limit),
        None => command.env_remove("STITCHWORT_WORK_LIMIT"),
    };
    command
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

#[test]
fn a_low_work_limit_reproduces_e_resource() {
    let path = source();

    for limit in [None, Some("not-a-number"), Some("0")] {
        let out = check(&path, limit);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "the file checks fine with the variable {limit:?}:\n{stderr}"
        );
        assert!(!stderr.contains("E-RESOURCE"), "{stderr}");
    }

    let out = check(&path, Some("100000"));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "100,000 steps are not enough for the theorem:\n{stderr}"
    );
    assert!(
        stderr.contains("E-RESOURCE"),
        "the failure is E-RESOURCE:\n{stderr}"
    );
    assert!(
        stderr.contains("countBig"),
        "E-RESOURCE names the computing declaration:\n{stderr}"
    );
}
