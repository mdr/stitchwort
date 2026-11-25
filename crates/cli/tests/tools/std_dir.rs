//! A missing standard library is a setup error the command reports, not a
//! panic (SW-1142).

use std::path::Path;
use std::process::{Command, Output, Stdio};

/// Runs `stitchwort` with `STITCHWORT_STD_DIR` naming `dir`.
fn stitchwort_with_std_dir(dir: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .env("STITCHWORT_STD_DIR", dir)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// `STITCHWORT_STD_DIR` naming a directory that doesn't exist: one clear
/// error saying what was looked for and how to point at a copy, exit 2, and
/// no panic text or backtrace note.
#[test]
fn a_missing_std_dir_is_a_clean_error() {
    let missing = "/nonexistent/stitchwort-std-for-test";
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/abort.sw");
    let output = stitchwort_with_std_dir(
        missing,
        &["check", &example.display().to_string(), "--no-cache"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "stderr:\n{stderr}");
    assert!(
        stderr.contains("the standard library at"),
        "stderr:\n{stderr}"
    );
    assert!(stderr.contains(missing), "stderr:\n{stderr}");
    assert!(stderr.contains("--std-dir"), "stderr:\n{stderr}");
    assert!(stderr.contains("STITCHWORT_STD_DIR"), "stderr:\n{stderr}");
    assert!(!stderr.contains("panicked"), "stderr:\n{stderr}");
    assert!(!stderr.contains("RUST_BACKTRACE"), "stderr:\n{stderr}");
}

/// `test --std Nat/Iterate.sw` runs the tests declared in that file and no
/// others, and a target that names no library file fails.
#[test]
fn test_std_runs_one_library_namespace_s_tests() {
    let run = |args: &[&str]| {
        let mut all = vec!["test", "--std"];
        all.extend_from_slice(args);
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(all)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort")
    };
    let output = run(&["Nat/Iterate.sw"]);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(output.status.success(), "stdout:\n{stdout}");
    assert!(stdout.contains("Nat.iterate dot"), "stdout:\n{stdout}");
    assert!(stdout.contains("2 test(s): 2 passed"), "stdout:\n{stdout}");
    assert!(!stdout.contains("divSuccStep"), "stdout:\n{stdout}");

    let output = run(&["Nope"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stderr:\n{stderr}");
    assert!(stderr.contains("E-STD-TARGET"), "stderr:\n{stderr}");
}

/// Copies the directory `from` to `to`, recursively.
fn copy_tree(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap().flatten() {
        let (source, target) = (entry.path(), to.join(entry.file_name()));
        if source.is_dir() {
            copy_tree(&source, &target);
        } else {
            std::fs::copy(&source, &target).unwrap();
        }
    }
}

/// The library's name index is read from the cache directory only for the
/// library it was made from (SW-4812): a name added to a file of a
/// `--std-dir` copy resolves on the next check, and is gone again once the
/// edit is undone, which finds the first index again.
#[test]
fn editing_a_std_dir_file_misses_the_cached_name_index() {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let scratch = std::env::temp_dir().join(format!(
        "stitchwort-index-std-dir-{}-{nanos}",
        std::process::id()
    ));
    let std = scratch.join("std");
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std"),
        &std,
    );
    let program = scratch.join("probe.sw");
    std::fs::write(
        &program,
        "import Std (Nat)\ndef probe: Nat := Nat.indexCacheProbe 3\n",
    )
    .unwrap();
    let cache = scratch.join("cache");
    let check = || {
        let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["--std-dir", &std.display().to_string(), "check"])
            .arg(&program)
            .arg("--cache-dir")
            .arg(&cache)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort");
        let text = String::from_utf8_lossy(&output.stdout).to_string()
            + &String::from_utf8_lossy(&output.stderr);
        (output.status.success(), text)
    };
    let indexes = || std::fs::read_dir(cache.join("std-index")).map_or(0, |d| d.count());

    let file = std.join("Nat/Iterate.sw");
    let original = std::fs::read_to_string(&file).unwrap();
    let (ok, text) = check();
    assert!(!ok, "no such name yet:\n{text}");
    assert!(text.contains("indexCacheProbe"), "{text}");
    assert_eq!(indexes(), 1, "the index is written");

    std::fs::write(
        &file,
        format!("{original}\ndef Nat.indexCacheProbe (n: Nat): Nat := n\n"),
    )
    .unwrap();
    let (ok, text) = check();
    assert!(ok, "the added name resolves:\n{text}");
    assert_eq!(indexes(), 2, "the edited library has an index of its own");

    std::fs::write(&file, &original).unwrap();
    let (ok, text) = check();
    assert!(!ok, "the name is gone again:\n{text}");
    assert_eq!(indexes(), 2, "the first index is found again");
    let _ = std::fs::remove_dir_all(&scratch);
}
