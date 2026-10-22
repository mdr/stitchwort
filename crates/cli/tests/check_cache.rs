//! The check cache (docs/proposals/check-cache.md) end to end, with the
//! built command: what `stitchwort check --index` prints (the navigation
//! index the editor reads, and the diagnostics) is byte for byte the same
//! from a warm cache as without one, and `stitchwort test` from a warm cache
//! neither elaborates nor runs anything.
//!
//! The canonical dump of the elaborator is compared in
//! `crates/driver/tests/check_cache.rs`; this checks what the user sees.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use stitchwort_cli::driver::{par_map, slow_tier, slow_tier_on};

/// A new, empty directory.
fn temp_dir(name: &str) -> PathBuf {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-cli-check-cache-{name}-{}-{n}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn stitchwort(args: &[&str], env: &[(&str, &str)]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .envs(env.iter().copied())
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// What a run printed, and how it ended.
fn shown(output: &Output) -> String {
    format!(
        "status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// The first line where two texts differ.
fn first_difference(a: &str, b: &str) -> String {
    for (i, (x, y)) in a.lines().zip(b.lines()).enumerate() {
        if x != y {
            let cut = |s: &str| s.chars().take(300).collect::<String>();
            return format!("line {i}:\n  fresh: {}\n  warm:  {}", cut(x), cut(y));
        }
    }
    format!(
        "one is a prefix of the other ({} and {} lines)",
        a.lines().count(),
        b.lines().count()
    )
}

/// The namespace entries in a cache directory.
fn namespace_entries(cache: &Path) -> usize {
    std::fs::read_dir(cache.join("check")).map_or(0, |entries| {
        entries
            .flatten()
            .filter(|e| e.file_name().to_string_lossy().contains("-ns."))
            .count()
    })
}

/// `check --index -` of `project` (and `namespaces` of it, if any) gives
/// the same output without a cache, writing one, and reading it.
fn assert_index_unchanged(project: &Path, cache: &Path, namespaces: &[&str]) -> Output {
    let root = project.to_str().unwrap();
    let cache_dir = cache.to_str().unwrap();
    let mut args = vec!["check", "--index", "-", "--project", root];
    args.extend(namespaces);
    let mut fresh_args = args.clone();
    fresh_args.push("--no-cache");
    let mut cached_args = args.clone();
    cached_args.extend(["--cache-dir", cache_dir]);
    let fresh = stitchwort(&fresh_args, &[]);
    let cold = stitchwort(&cached_args, &[]);
    let warm = stitchwort(&cached_args, &[]);
    let name = format!("{} {namespaces:?}", project.display());
    for (what, run) in [("cold", &cold), ("warm", &warm)] {
        assert!(
            shown(run) == shown(&fresh),
            "{name}: the {what} run printed something else: {}",
            first_difference(&shown(&fresh), &shown(run))
        );
    }
    warm
}

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

/// Every example project, accepted and rejected. Outside the slow tier,
/// every fourth (a fixed sample).
fn example_projects() -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    for kind in ["accept", "reject"] {
        let root = examples_dir().join("projects").join(kind);
        let mut found: Vec<PathBuf> = std::fs::read_dir(&root)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.is_dir())
            .collect();
        found.sort();
        dirs.extend(found);
    }
    assert!(!dirs.is_empty());
    if slow_tier_on() {
        dirs
    } else {
        dirs.into_iter().step_by(4).collect()
    }
}

#[test]
fn the_index_is_the_same_from_the_cache_for_the_example_projects() {
    let projects = example_projects();
    par_map(1024 * 1024, &projects, |project| {
        let cache = temp_dir("examples");
        let warm = assert_index_unchanged(project, &cache, &[]);
        if warm.status.success() {
            assert!(
                namespace_entries(&cache) > 0,
                "{}: no namespace was cached",
                project.display()
            );
        }
        let _ = std::fs::remove_dir_all(&cache);
    });
}

/// `aoc`, as the editor checks it: the whole project on opening, then one
/// namespace on each save (`editors/vscode/extension.js`).
#[test]
fn the_index_is_the_same_from_the_cache_for_aoc() {
    if !slow_tier("the_index_is_the_same_from_the_cache_for_aoc") {
        return;
    }
    let aoc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let cache = temp_dir("aoc");
    assert_index_unchanged(&aoc, &cache, &[]);
    let whole = namespace_entries(&cache);
    assert!(whole > 10, "{whole} namespaces cached");
    // A namespace on its own, from the entries the whole project wrote:
    // nothing more is written.
    assert_index_unchanged(&aoc, &cache, &["Aoc.Day05"]);
    assert_eq!(namespace_entries(&cache), whole);
    let _ = std::fs::remove_dir_all(&cache);
}

/// One command writes the cache and another reads it (SW-255): `check`
/// then `run`, `run` then `check`, and so on. Each prints what it prints
/// without a cache. `A` loads `std/Fin/Fin.sw` before `B` in a whole
/// project check; `run B.main` checks only `B`, which then has to load it
/// itself.
#[test]
fn commands_share_one_cache() {
    let project = temp_dir("commands-project");
    let write = |path: &str, text: &str| {
        let full = project.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    };
    write("stitchwort.yaml", "sources: [src]\n");
    write(
        "src/A.sw",
        "namespace A\nimport Std (Fin)\n\ndef two: Fin 3 := Fin.ofNat 2\n",
    );
    write(
        "src/B/B.sw",
        "namespace B\nimport Std (Fin, IO)\n\ndef three: Fin 4 := Fin.ofNat 3\n\n\
         def main(): {IO} () := IO.print \"three is ${three}\"\n",
    );
    write(
        "src/B/Tests/Tests.sw",
        "namespace B.Tests\nimport B (three)\nimport Std (Fin)\n\n\
         test \"three\" := Fin.toNat three == 3\n",
    );
    write(
        "src/B/Proofs/Proofs.sw",
        "namespace B.Proofs\nimport B (three)\nimport Std (Fin)\n\n\
         theorem threeIsThree: Fin.toNat three = 3 := rfl\n",
    );
    let root = project.to_str().unwrap();
    let command = |words: &[&str]| -> Vec<String> {
        let mut args: Vec<String> = words.iter().map(|w| w.to_string()).collect();
        args.extend(["--project".to_string(), root.to_string()]);
        args
    };
    let check = command(&["check"]);
    let check_b = command(&["check", "B"]);
    let check_tests = command(&["check", "B.Tests"]);
    let run = command(&["run", "B.main"]);
    let test = command(&["test"]);
    let run_args = |args: &[String], extra: &[&str]| {
        let mut all: Vec<&str> = args.iter().map(String::as_str).collect();
        all.extend(extra);
        stitchwort(&all, &[])
    };
    let fresh = |args: &[String]| shown(&run_args(args, &["--no-cache"]));
    let ran = fresh(&run);
    assert!(ran.contains("three is 3"), "{ran}");
    for args in [&check, &test] {
        let out = fresh(args);
        assert!(out.starts_with("status Some(0)"), "{out}");
    }
    for sequence in [
        [&check, &run],
        [&check, &test],
        [&run, &check],
        [&check_b, &run],
        [&check_tests, &run],
        [&run, &test],
        [&test, &run],
    ] {
        let cache = temp_dir("commands-cache");
        let cache_dir = cache.to_str().unwrap();
        // The commands without `--project`.
        let words = |args: &[String]| args[..args.len() - 2].join(" ");
        let what = sequence.map(|args| words(args)).join(", then ");
        for args in sequence {
            let cached = shown(&run_args(args, &["--cache-dir", cache_dir]));
            let expected = fresh(args);
            assert!(
                cached == expected,
                "{what}: `{}` printed something else from the cache: {}",
                words(args),
                first_difference(&expected, &cached)
            );
        }
        let _ = std::fs::remove_dir_all(&cache);
    }
    let _ = std::fs::remove_dir_all(&project);
}

/// `stitchwort test` from a warm cache loads the namespaces from the check
/// cache and the results from the test cache.
#[test]
fn a_warm_test_run_elaborates_and_runs_nothing() {
    let project = temp_dir("test-project");
    std::fs::write(project.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::create_dir_all(project.join("src")).unwrap();
    std::fs::write(
        project.join("src/Lib.sw"),
        "namespace Lib\n\ndef double (n: Nat): Nat := n + n\n\ntest \"double\" := double 2 == 4\n",
    )
    .unwrap();
    std::fs::write(
        project.join("src/App.sw"),
        "namespace App\n\nimport Lib (double)\n\ntest \"twice\" := double (double 1) == 4\n",
    )
    .unwrap();
    let cache = temp_dir("test-cache");
    let args = [
        "test",
        "--project",
        project.to_str().unwrap(),
        "--cache-dir",
        cache.to_str().unwrap(),
    ];
    let timings = [("STITCHWORT_TIMINGS", "1")];
    let cold = stitchwort(&args, &timings);
    assert!(cold.status.success(), "{}", shown(&cold));
    let out = String::from_utf8_lossy(&cold.stdout).to_string();
    assert!(
        out.contains("2 test(s): 2 passed, 0 failed (0 from the cache)"),
        "{out}"
    );
    let warm = stitchwort(&args, &timings);
    assert!(warm.status.success(), "{}", shown(&warm));
    let out = String::from_utf8_lossy(&warm.stdout).to_string();
    assert!(
        out.contains("2 test(s): 2 passed, 0 failed (2 from the cache)"),
        "{out}"
    );
    let err = String::from_utf8_lossy(&warm.stderr).to_string();
    for ns in ["Lib", "App"] {
        assert!(err.contains(&format!("{ns} (cached)")), "{err}");
    }
    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&cache);
}
