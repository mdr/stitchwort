//! `check` that stops before finishing says so and exits 3 (SW-4032): a
//! resource limit or a signal from outside (an outer `timeout`, or Ctrl-C).
//! An internal budget that gives up is an ordinary error, in a check that
//! finished, and still exits 1.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::Duration;

/// A project folder named `proj` in a fresh temporary folder for `test`.
fn project(test: &str, files: &[(&str, &str)]) -> PathBuf {
    let base = std::env::temp_dir().join(format!("stitchwort-early-{}-{test}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("proj");
    for (path, text) in files {
        let full = dir.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    }
    dir
}

fn stitchwort(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).to_string()
}

/// An internal budget that gave up is an error in a check that finished:
/// `rewrite repeatedly` made its 500 rewrites, so the proof failed, but the
/// check itself completed.
const BUDGET: &str = "import Std (Nat)\n\n\
                      theorem bad ∀ (a b: Nat) (there: a = b) (back: b = a): a + 1 = b + 1 :=\n\
                      \x20 rewrite repeatedly [there, back]\n";

#[test]
fn a_budget_error_exits_one_without_an_early_stop_line() {
    let dir = project("budget", &[("budget.sw", BUDGET)]);
    let out = stitchwort(&dir, &["check", "--no-cache", "budget.sw"]);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("E-REWRITE-REPEATEDLY-BUDGET"),
        "the budget isn't named:\n{stderr}"
    );
    assert!(
        !stderr.contains("check stopped early:"),
        "a budget error isn't a check that stopped early:\n{stderr}"
    );
}

/// A resource limit (a value too large to write out) stopped the check, and
/// the line says which declaration it was checking.
const RESOURCE: &str = "import Std (Eq, Nat)\n\n\
                        type Tree =\n  | Leaf (n: Nat)\n  | Node (left: Tree) (right: Tree)\n\n\
                        def grow: Nat → Tree → Tree\n  | Zero, tree => tree\n  \
                        | Succ n, tree => grow n (Node tree tree)\n\n\
                        theorem big (x: Nat) (t: Tree) (same: t = grow 30 (Leaf x)) \
                        (p: Tree → Prop) (h: p t): p (grow 30 (Leaf x)) :=\n\
                        \x20 rewrite same then h\n";

#[test]
fn a_check_stopped_by_a_resource_limit_says_where_and_exits_three() {
    let dir = project("resource", &[("resource.sw", RESOURCE)]);
    let out = stitchwort(&dir, &["check", "--no-cache", "resource.sw"]);
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(3), "{stderr}");
    assert!(
        stderr.contains("check stopped early: ran out of resources"),
        "no line saying it ran out:\n{stderr}"
    );
    assert!(
        stderr.contains("while checking `big`"),
        "the declaration isn't named:\n{stderr}"
    );
}

/// A check that takes long enough to signal: `count 3000000` runs past the
/// recursion limit, which takes seconds even in a debug build.
const SLOW: &str = "import Std (Eq, Nat)\n\n\
                    def count: Nat → Nat\n  | Zero => Zero\n  | Succ n => Succ (count n)\n\n\
                    theorem countBig: count 3000000 = 3000000 := byComputing\n";

#[cfg(unix)]
#[test]
fn a_signal_that_stops_a_check_says_so_and_exits_three() {
    use nix::sys::signal::{Signal, kill};
    use nix::unistd::Pid;

    let dir = project("signal", &[("slow.sw", SLOW)]);
    let child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache", "slow.sw"])
        .current_dir(&dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn stitchwort");
    // Its handler is installed before it starts checking; this is still
    // long before the check would finish.
    std::thread::sleep(Duration::from_secs(1));
    kill(Pid::from_raw(child.id() as i32), Signal::SIGTERM).expect("send SIGTERM");
    let out = child.wait_with_output().expect("wait for stitchwort");
    let stderr = text(&out.stderr);
    assert_eq!(out.status.code(), Some(3), "{stderr}");
    assert!(
        stderr.contains("check stopped early: stopped by SIGTERM"),
        "no line saying a signal stopped it:\n{stderr}"
    );
}
