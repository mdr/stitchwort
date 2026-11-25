//! `stitchwort dev keys` and `dev cache-compare` (SW-4822, SW-4839): the
//! keys they print are the names of the entries `check` writes, and two
//! cache folders compare by unit and key without the build prefix or the
//! build-specific entries.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let dir = std::env::temp_dir().join(format!(
            "stitchwort-dev-cache-{}-{name}",
            std::process::id()
        ));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(dir.join("proj/src")).expect("make a project");
        std::fs::write(dir.join("proj/stitchwort.yaml"), "sources: [src]\n").unwrap();
        write(&dir, "A", "def one: Nat := 1\n");
        std::fs::write(
            dir.join("proj/src/B.sw"),
            "namespace B\nimport A (one)\ndef two: Nat := one + 1\n",
        )
        .unwrap();
        Scratch(dir)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).ok();
    }
}

fn write(dir: &Path, namespace: &str, body: &str) {
    std::fs::write(
        dir.join(format!("proj/src/{namespace}.sw")),
        format!("namespace {namespace}\n{body}"),
    )
    .unwrap();
}

fn run(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .current_dir(dir.join("proj"))
        .env("STITCHWORT_JOBS", "1")
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

fn stdout(output: &Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout.clone()).unwrap()
}

/// The names of the project namespaces' entries in `cache`, without the
/// build prefix.
fn namespace_entries(cache: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(cache.join("check"))
        .unwrap()
        .flatten()
        .filter_map(|e| e.file_name().into_string().ok())
        .filter_map(|n| n.split_once('-').map(|(_, rest)| rest.to_string()))
        .filter(|rest| rest.starts_with("ns."))
        .collect();
    names.sort();
    names
}

#[test]
fn the_keys_printed_are_the_entries_check_writes() {
    let scratch = Scratch::new("keys");
    let cache = scratch.0.join("check-cache");
    run(
        &scratch.0,
        &["check", "--cache-dir", &cache.display().to_string()],
    );
    let written = namespace_entries(&cache);
    assert_eq!(written.len(), 2, "{written:?}");

    let explained = scratch.0.join("keys-cache");
    let out = stdout(&run(
        &scratch.0,
        &[
            "dev",
            "keys",
            "--cache-dir",
            &explained.display().to_string(),
        ],
    ));
    let printed: Vec<String> = out
        .lines()
        .filter(|l| !l.starts_with('\t'))
        .map(|l| {
            l.split('\t')
                .nth(1)
                .unwrap()
                .strip_prefix("entry ")
                .unwrap()
                .to_string()
        })
        .collect();
    assert_eq!(printed, written, "{out}");
    assert!(out.contains("B\t"), "{out}");
    assert!(out.contains("\tuses A\n\tdepends on A\n"), "{out}");
    assert!(out.contains("\tuses nothing\n"), "{out}");
}

#[test]
fn two_caches_of_the_same_project_compare_equal_without_the_build_entries() {
    let scratch = Scratch::new("same");
    let (a, b) = (scratch.0.join("a"), scratch.0.join("b"));
    // `check` also writes the scan and `ran` entries; `dev keys` doesn't.
    run(
        &scratch.0,
        &["check", "--cache-dir", &a.display().to_string()],
    );
    stdout(&run(
        &scratch.0,
        &["dev", "keys", "--cache-dir", &b.display().to_string()],
    ));
    let out = stdout(&run(
        &scratch.0,
        &[
            "dev",
            "cache-compare",
            &a.display().to_string(),
            &b.display().to_string(),
        ],
    ));
    assert!(
        out.contains("only in A: 0\nonly in B: 0\nsame: 2\n"),
        "{out}"
    );
    assert!(out.contains("A 1 scan; B none"), "{out}");
}

#[test]
fn an_edited_namespace_changes_its_entry_and_its_dependents() {
    let scratch = Scratch::new("edit");
    let (a, b) = (scratch.0.join("a"), scratch.0.join("b"));
    stdout(&run(
        &scratch.0,
        &["dev", "keys", "--cache-dir", &a.display().to_string()],
    ));
    write(&scratch.0, "A", "def one: Nat := 1\ndef three: Nat := 3\n");
    stdout(&run(
        &scratch.0,
        &["dev", "keys", "--cache-dir", &b.display().to_string()],
    ));
    let output = run(
        &scratch.0,
        &[
            "dev",
            "cache-compare",
            &a.display().to_string(),
            &b.display().to_string(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let out = String::from_utf8(output.stdout).unwrap();
    assert!(out.contains("only in A: 2\n  ns.A-"), "{out}");
    assert!(out.contains("only in B: 2\n  ns.A-"), "{out}");
    assert!(out.contains("same: 0\n"), "{out}");
    assert!(out.matches("  ns.B-").count() == 2, "{out}");
}
