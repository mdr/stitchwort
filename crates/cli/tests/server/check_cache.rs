//! The check cache (docs/proposals/check-cache.md) end to end, with the
//! built command: what `stitchwort check --index` prints (the navigation
//! index the editor reads, and the diagnostics) is byte for byte the same
//! from a warm cache as without one, and `stitchwort test` from a warm cache
//! neither elaborates nor runs anything.
//!
//! The canonical dump of the elaborator is compared in
//! `crates/driver/tests/projects/check_cache.rs`; this checks what the user sees.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use stitchwort_cli::driver::{all_tier, par_map, tier_sample};

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

/// Each namespace's entry in a cache directory, by namespace: its key.
fn namespace_entry_keys(cache: &Path) -> std::collections::BTreeMap<String, String> {
    let mut found = std::collections::BTreeMap::new();
    for entry in std::fs::read_dir(cache.join("check")).unwrap().flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        if let Some((_, rest)) = name.split_once("-ns.")
            && let Some((unit, key)) = rest.rsplit_once('-')
        {
            found.insert(unit.to_string(), key.to_string());
        }
    }
    found
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
    tier_sample(dirs, 4)
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
    if !all_tier("the_index_is_the_same_from_the_cache_for_aoc") {
        return;
    }
    let aoc = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let cache = temp_dir("aoc");
    assert_index_unchanged(&aoc, &cache, &[]);
    let whole = namespace_entries(&cache);
    assert!(whole > 10, "{whole} namespaces cached");
    // A namespace on its own, from the entries the whole project wrote:
    // nothing more is written.
    assert_index_unchanged(&aoc, &cache, &["Aoc.Year2025.Day05"]);
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

// ---- A plain `check` leaves out what it doesn't need (SW-1193) ------------

/// `check` of `project` with a cache in `cache`: with `skip`, as it runs
/// by default (it reports the namespaces it doesn't need to load from their
/// entries); without, as `STITCHWORT_SKIP_UNNEEDED=0` (it loads them all).
fn plain_check(project: &Path, cache: &Path, skip: bool, debug: bool) -> Output {
    let mut env = vec![("STITCHWORT_SKIP_UNNEEDED", if skip { "1" } else { "0" })];
    if debug {
        env.push(("STITCHWORT_CACHE_DEBUG", "1"));
    }
    stitchwort(
        &[
            "check",
            "--project",
            project.to_str().unwrap(),
            "--cache-dir",
            cache.to_str().unwrap(),
        ],
        &env,
    )
}

/// The namespaces a debug run of [`plain_check`] says it didn't load.
fn skipped(output: &Output) -> Vec<String> {
    let mut names: Vec<String> = String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter_map(|l| {
            l.strip_prefix("check cache: ")?
                .strip_suffix(": reported from its entry, not loaded")
                .map(str::to_string)
        })
        .collect();
    names.sort();
    names
}

/// Runs a plain `check` of `project` with and without leaving out the
/// namespaces it doesn't need, each with its own cache, and asserts they
/// print the same. The namespaces left out.
fn assert_skipping_unchanged(
    project: &Path,
    skipping: &Path,
    loading: &Path,
    what: &str,
) -> Vec<String> {
    let with = plain_check(project, skipping, true, true);
    let without = plain_check(project, loading, false, false);
    let left_out = skipped(&with);
    // The debug lines aside.
    let with_err: String = String::from_utf8_lossy(&with.stderr)
        .lines()
        .filter(|l| !l.starts_with("check cache: "))
        .map(|l| format!("{l}\n"))
        .collect();
    let with_shown = format!(
        "status {:?}\nstdout:\n{}\nstderr:\n{}",
        with.status.code(),
        String::from_utf8_lossy(&with.stdout),
        with_err
    );
    assert!(
        with_shown == shown(&without),
        "{} ({what}): skipping {left_out:?} printed something else: {}\n{with_shown}",
        project.display(),
        first_difference(&shown(&without), &with_shown)
    );
    left_out
}

/// Every example project (a sample outside the slow tier), warm: the
/// plain `check` that leaves out what it can prints what loading
/// everything prints.
#[test]
fn plain_check_skipping_unneeded_namespaces_is_the_same_for_the_example_projects() {
    let projects = example_projects();
    par_map(1024 * 1024, &projects, |project| {
        let skipping = temp_dir("skip-examples-on");
        let loading = temp_dir("skip-examples-off");
        for what in ["cold", "warm"] {
            assert_skipping_unchanged(project, &skipping, &loading, what);
        }
        let _ = std::fs::remove_dir_all(&skipping);
        let _ = std::fs::remove_dir_all(&loading);
    });
}

/// A small project through a series of edits: a plain `check` that leaves
/// out the namespaces nothing re-checked needs prints what loading them
/// all prints, each time, and leaves out what it should. `Base` and
/// `Other` have a warning, kept in their entries; `Mid` has doc links,
/// one into `Leaf`, which can change without `Mid`'s key changing.
#[test]
fn plain_check_skipping_unneeded_namespaces_is_the_same_after_edits() {
    let project = temp_dir("skip-project");
    let write = |path: &str, text: &str| {
        let full = project.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    };
    let shadow = "import Std (List)\nimport List (map)\n\n\
                  def shadowed: (Nat → Nat) → List Nat → List Nat := map xs => List.map xs map\n";
    let base = format!("namespace Base\n{shadow}\ndef one: Nat := 1\n");
    let mid = "namespace Mid\nimport Base (one)\n\n\
               --| Twice [`one`]; see [`Leaf.thing`].\ndef two: Nat := one + one\n";
    let leaf = "namespace Leaf\nimport Mid (two)\n\ntheorem twoIsTwo: two = 2 := rfl\n";
    let other = format!("namespace Other\n{shadow}\ndef three: Nat := 3\n");
    let other_tests =
        "namespace Other.Tests\nimport Other (three)\n\ntest \"three\" := three == 3\n";
    write("stitchwort.yaml", "sources: [src]\n");
    write("src/Base.sw", &base);
    write("src/Mid/Mid.sw", mid);
    write("src/Leaf/Leaf.sw", leaf);
    write("src/Other/Other.sw", &other);
    write("src/Other/Tests/Tests.sw", other_tests);
    let skipping = temp_dir("skip-cache-on");
    let loading = temp_dir("skip-cache-off");
    let check = |what: &str| assert_skipping_unchanged(&project, &skipping, &loading, what);
    let names = |ns: &[&str]| ns.iter().map(|n| n.to_string()).collect::<Vec<_>>();

    assert_eq!(check("cold"), names(&[]));
    // Warm: all but `Mid` (doc links) and `Base` (which it uses).
    assert_eq!(check("warm"), names(&["Leaf", "Other", "Other.Tests"]));
    write("src/Leaf/Leaf.sw", &format!("{leaf}-- touched\n"));
    assert_eq!(check("a leaf edited"), names(&["Other", "Other.Tests"]));
    // `Mid`'s link to `Leaf.thing` resolves now, though its key is the same.
    write(
        "src/Leaf/Leaf.sw",
        &format!("{leaf}\ndef thing: Nat := 4\n"),
    );
    assert_eq!(
        check("a linked name added"),
        names(&["Other", "Other.Tests"])
    );
    write("src/Base.sw", &format!("{base}-- touched\n"));
    assert_eq!(check("the base edited"), names(&["Other", "Other.Tests"]));
    write(
        "src/Other/Other.sw",
        &format!("{other}\ndef bad: Nat := thing\n"),
    );
    // `Leaf` comes before `Other`, whose error's notes may name any
    // namespace checked before it, so everything is loaded.
    assert_eq!(check("an error"), names(&[]));
    write("src/Other/Other.sw", &other);
    write(
        "src/Mid/Mid.sw",
        &format!("{mid}\ntheorem open: one = 1 := ?\n"),
    );
    assert_eq!(check("a goal"), names(&["Other", "Other.Tests"]));
    write("src/Mid/Mid.sw", mid);
    write("src/Other/Other.sw", &format!("{other}\ndef := \n"));
    // `Leaf`'s entry is for the `Mid` with a goal: the cache keeps one
    // entry per namespace.
    assert_eq!(check("a syntax error"), names(&[]));
    write("src/Other/Other.sw", &other);
    assert_eq!(check("fixed"), names(&["Leaf", "Other", "Other.Tests"]));
    // The project's namespaces are part of every key.
    std::fs::remove_file(project.join("src/Other/Tests/Tests.sw")).unwrap();
    assert_eq!(check("a file deleted"), names(&[]));
    assert_eq!(check("warm again"), names(&["Leaf", "Other"]));
    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&skipping);
    let _ = std::fs::remove_dir_all(&loading);
}

/// A namespace entry that can't be read is a miss when the plain `check`
/// plans what to load: the namespace is checked again, not left out, and
/// so is what uses it; what is printed is what loading everything prints.
#[test]
fn plain_check_checks_a_namespace_whose_entry_is_corrupt() {
    let project = temp_dir("skip-corrupt-project");
    let write = |path: &str, text: &str| {
        let full = project.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    };
    write("stitchwort.yaml", "sources: [src]\n");
    write(
        "src/Lib.sw",
        "namespace Lib\n\ndef double (n: Nat): Nat := n + n\n",
    );
    write(
        "src/App.sw",
        "namespace App\nimport Lib (double)\n\ntheorem four: double 2 = 4 := rfl\n",
    );
    write("src/Solo.sw", "namespace Solo\n\ndef five: Nat := 5\n");
    let skipping = temp_dir("skip-corrupt-on");
    let loading = temp_dir("skip-corrupt-off");
    let check = |what: &str| assert_skipping_unchanged(&project, &skipping, &loading, what);
    let names = |ns: &[&str]| ns.iter().map(|n| n.to_string()).collect::<Vec<_>>();
    check("cold");
    assert_eq!(check("warm"), names(&["App", "Lib", "Solo"]));
    let entry = |ns: &str| -> PathBuf {
        let found: Vec<PathBuf> = std::fs::read_dir(skipping.join("check"))
            .unwrap()
            .flatten()
            .map(|e| e.path())
            .filter(|p| (p.file_name().unwrap().to_string_lossy()).contains(&format!("-ns.{ns}-")))
            .collect();
        assert_eq!(found.len(), 1, "{found:?}");
        found[0].clone()
    };
    // A byte flipped in the middle of `Solo`'s entry (each run rewrites it).
    let flip = |path: &Path| {
        let mut bytes = std::fs::read(path).unwrap();
        let middle = bytes.len() / 2;
        bytes[middle] ^= 0xff;
        std::fs::write(path, &bytes).unwrap();
    };
    flip(&entry("Solo"));
    assert_eq!(check("Solo's entry corrupt"), names(&["App", "Lib"]));
    // Cut short.
    let lib = entry("Lib");
    let bytes = std::fs::read(&lib).unwrap();
    std::fs::write(&lib, &bytes[..bytes.len() / 3]).unwrap();
    assert_eq!(check("Lib's entry cut short"), names(&["Solo"]));
    // Gone.
    std::fs::remove_file(entry("App")).unwrap();
    assert_eq!(check("App's entry gone"), names(&["Solo"]));
    assert_eq!(check("warm again"), names(&["App", "Lib", "Solo"]));
    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&skipping);
    let _ = std::fs::remove_dir_all(&loading);
}

// ---- Edits to the standard library (SW-1330) ----------------------------

/// Copies the directory `from` to `to`.
fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap().flatten() {
        let target = to.join(entry.file_name());
        if entry.path().is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), target).unwrap();
        }
    }
}

/// A plain `check` of `project` reading the library from `std_dir`, with a
/// cache in `cache` or without (`--no-cache`): what it printed, the debug
/// lines aside, and the namespaces it elaborated because their entries
/// didn't fit.
fn check_with_std(project: &Path, std_dir: &Path, cache: Option<&Path>) -> (String, Vec<String>) {
    let mut args = vec!["check", "--project", project.to_str().unwrap()];
    match cache {
        Some(dir) => args.extend(["--cache-dir", dir.to_str().unwrap()]),
        None => args.push("--no-cache"),
    }
    let output = stitchwort(
        &args,
        &[
            ("STITCHWORT_STD_DIR", std_dir.to_str().unwrap()),
            ("STITCHWORT_CACHE_DEBUG", "1"),
        ],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    let mut missed: Vec<String> = stderr
        .lines()
        .filter_map(|l| {
            let (name, _) = l.strip_prefix("check cache: ")?.split_once(": a miss")?;
            Some(name.to_string())
        })
        .collect();
    missed.sort();
    missed.dedup();
    let printed = format!(
        "status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        stderr
            .lines()
            .filter(|l| !l.starts_with("check cache: "))
            .map(|l| format!("{l}\n"))
            .collect::<String>()
    );
    (printed, missed)
}

/// A project with `files`, a copy of the library to edit, and an empty cache.
fn std_edit_fixture(name: &str, files: &[(&str, &str)]) -> (PathBuf, PathBuf, PathBuf) {
    let project = temp_dir(name);
    std::fs::write(project.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
    std::fs::create_dir_all(project.join("src")).unwrap();
    for (path, text) in files {
        std::fs::write(project.join(path), text).unwrap();
    }
    let std_dir = temp_dir(&format!("{name}-std"));
    copy_dir(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std"),
        &std_dir,
    );
    (project, std_dir, temp_dir(&format!("{name}-cache")))
}

/// A `check` of `project` from `cache` prints what a fresh one does, and
/// elaborates `expect` again. A namespace is elaborated again if its entry
/// didn't fit (a miss), or its key changed so that there was none to try.
/// (One with errors writes no entry, so only its output shows it.)
fn check_step(
    (project, std_dir, cache): (&Path, &Path, &Path),
    what: &str,
    expect: &[&str],
) -> String {
    let (fresh, _) = check_with_std(project, std_dir, None);
    let before = if cache.join("check").exists() {
        namespace_entry_keys(cache)
    } else {
        Default::default()
    };
    let (cached, mut missed) = check_with_std(project, std_dir, Some(cache));
    for (unit, key) in namespace_entry_keys(cache) {
        if before.get(&unit).is_some_and(|old| *old != key) {
            missed.push(unit);
        }
    }
    missed.sort();
    missed.dedup();
    assert!(
        cached == fresh,
        "{what}: the cache changed what `check` prints: {}",
        first_difference(&fresh, &cached)
    );
    assert_eq!(missed, expect, "{what}: namespaces elaborated again");
    fresh
}

/// Replaces the first `from` in the library file `file` of `std_dir`.
fn edit_std(std_dir: &Path, file: &str, from: &str, to: &str) {
    let path = std_dir.join(file);
    let old = std::fs::read_to_string(&path).unwrap();
    assert!(old.contains(from), "{file} has no `{from}`");
    std::fs::write(path, old.replacen(from, to, 1)).unwrap();
}

/// `B` never names `Option`'s lemma file, but its `rewrite` needs
/// `Option.mapCong`, which lives in the file of `Option.map`; `A` loads the
/// lemma file too. An edit to `Option.mapCong` must reach `B`'s entry
/// (SW-1354 makes a result independent of what else the run loads, so the
/// entry's list of the files it needs is enough).
#[test]
fn an_entry_is_a_miss_when_a_library_file_loaded_beside_it_changed() {
    let (project, std_dir, cache) = std_edit_fixture(
        "std-lookup",
        &[
            (
                "src/A.sw",
                "namespace A\nimport Std (Option)\n\n\
                 theorem idem (x: Option Nat): Option.map x (y => y) = x := Option.mapId x\n",
            ),
            (
                "src/B.sw",
                "namespace B\nimport Std (Option)\n\ndef inc (x: Nat): Nat := Succ x\n\n\
                 theorem incIs (x: Nat): inc x = Succ x := rfl\n\n\
                 theorem t (o: Option Nat): Option.map o (x => inc x) = Option.map o (x => Succ x) := \
                 rewrite incIs\n",
            ),
        ],
    );
    let dirs = (&*project, &*std_dir, &*cache);
    check_step(dirs, "cold", &[]);
    check_step(dirs, "warm", &[]);
    edit_std(
        &std_dir,
        "Option/Option.sw",
        "Option.map x f1 = Option.map x f2 :=\n  match x with\n    | None => rfl\n    | Some y => Eq.cong Some (ef y)",
        "Option.map x f1 = Option.map x f1 :=\n  match x with\n    | None => rfl\n    | Some y => rfl",
    );
    let after = check_step(dirs, "a lemma found by lookup changed", &["A", "B"]);
    assert!(after.contains("E-REWRITE-CONG"), "{after}");
    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&std_dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// An edit to the library's text reaches exactly the namespaces whose
/// results it can change, and the cache never hides what a fresh check
/// reports (the check cache's key holds no copy of the library's text; it
/// holds the core, the library's names, and the text of the files a
/// namespace loads).
#[test]
fn a_library_edit_re_checks_what_it_can_change_and_nothing_else() {
    let files: &[(&str, &str)] = &[
        ("src/Plain.sw", "namespace Plain\n\ndef three: Nat := 3\n"),
        (
            "src/Fancy.sw",
            "namespace Fancy\nimport Std (Ansi)\n\ndef hi: Text := Ansi.bold \"hi\"\n\n\
                 theorem hi_is: hi = \"\\u{1b}[1mhi\\u{1b}[22m\" := rfl\n",
        ),
        (
            "src/Sum.sw",
            "namespace Sum\n\ndef six: Nat := [1, 2, 3].sumBy (x => x)\n\n\
                 theorem six_is_six: six = 6 := rfl\n",
        ),
        // Uses no library file itself, but depends on `Wild.hi`, whose hash
        // the `Ansi` edit changes, so its entry misses through that
        // dependency.
        (
            "src/Dep.sw",
            "namespace Dep\nimport Wild (hi)\n\ndef again: Text := hi\n",
        ),
        // Both files declare `bold`, but only `Ansi`'s is used.
        (
            "src/Wild.sw",
            "namespace Wild\nimport Std.Ansi (..)\nimport Std.Key (..)\n\n\
                 def hi: Text := bold \"hi\"\n",
        ),
    ];
    let (project, std_dir, cache) = std_edit_fixture("std-edit", files);
    let dirs = (&*project, &*std_dir, &*cache);
    let check = |what: &str, expect: &[&str]| check_step(dirs, what, expect);
    let append = |file: &str, text: &str| {
        let path = std_dir.join(file);
        let old = std::fs::read_to_string(&path).unwrap();
        std::fs::write(path, old + text).unwrap();
    };
    let replace = |file: &str, from: &str, to: &str| edit_std(&std_dir, file, from, to);

    let first = check("cold", &[]);
    assert!(first.contains("status Some(0)"), "{first}");
    assert_eq!(namespace_entries(&cache), 5);
    check("warm", &[]);

    // A comment in a file no namespace loads: its text isn't in their keys.
    append("Graph/Search.sw", "\n-- a comment\n");
    check("a comment in a file nothing loads", &[]);

    // A body that `Fancy` and `Wild` use (through `Ansi`) changes, and so
    // does `Dep`, which depends on `Wild`; `Plain` and `Sum` load nothing
    // that reaches it. `Fancy`'s theorem now fails.
    replace("Terminal/Ansi.sw", "\\u{1b}[1m${text}", "\\u{1b}[2m${text}");
    let after = check(
        "a used definition's body changed",
        &["Dep", "Fancy", "Wild"],
    );
    assert!(after.contains("E-REFL"), "{after}");

    // A name nothing uses is added, to a file nothing loads: a name can make
    // a short name ambiguous in a namespace that never writes it (`Wild`'s
    // `bold`), so every namespace is checked again. (`Fancy` and `Wild` have
    // errors, so write no entries.)
    append("Terminal/Key.sw", "\ndef Key.bold: Nat := 1\n");
    let after = check("a name added", &["Plain", "Sum"]);
    assert!(after.contains("E-AMBIGUOUS"), "{after}");
    assert!(after.contains("E-REFL"), "{after}");

    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&std_dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// A namespace's result doesn't depend on which library files the other
/// namespaces of the run load (SW-1354). `B` rewrites inside `Option.map`,
/// which needs `Option.mapCong`; `A` loads `Option/Lemmas.sw` (for
/// `Option.mapId`) and `B` doesn't. `B` checks the same alone, beside an
/// `A` that loads that file and beside one that doesn't: fresh, with a cold
/// cache and with a warm one.
#[test]
fn a_namespace_checks_the_same_whatever_else_the_run_loads() {
    let b = "namespace B\nimport Std (Option)\n\ndef inc (x: Nat): Nat := Succ x\n\n\
             theorem incIs (x: Nat): inc x = Succ x := rfl\n\n\
             theorem t (o: Option Nat): Option.map o (x => inc x) = Option.map o (x => Succ x) := \
             rewrite incIs\n";
    let lemmas = "namespace A\nimport Std (Option)\n\n\
                  theorem idem (x: Option Nat): Option.map x (y => y) = x := Option.mapId x\n";
    let plain = "namespace A\n\ndef one: Nat := 1\n";
    for (what, a) in [
        ("alone", None),
        ("with A", Some(lemmas)),
        ("with a plain A", Some(plain)),
    ] {
        let project = temp_dir("loads-project");
        std::fs::create_dir_all(project.join("src")).unwrap();
        std::fs::write(project.join("stitchwort.yaml"), "sources: [src]\n").unwrap();
        std::fs::write(project.join("src/B.sw"), b).unwrap();
        if let Some(a) = a {
            std::fs::write(project.join("src/A.sw"), a).unwrap();
        }
        let namespaces = if a.is_some() { 2 } else { 1 };
        let cache = temp_dir("loads-cache");
        let dir = project.to_str().unwrap();
        let fresh = stitchwort(&["check", "--project", dir, "--no-cache"], &[]);
        let runs = [
            ("fresh", fresh),
            ("cold", plain_check(&project, &cache, true, false)),
            ("warm", plain_check(&project, &cache, true, false)),
        ];
        for (when, output) in &runs {
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                output.status.success()
                    && stderr.contains(&format!("checked {namespaces} namespace")),
                "{what}, {when}: {}",
                shown(output)
            );
        }
        let _ = std::fs::remove_dir_all(&project);
        let _ = std::fs::remove_dir_all(&cache);
    }
}

/// `check --std` loads the library file it names and checks its bodies,
/// even from a warm cache, and a program that never names the file doesn't
/// see the edit (SW-2863: the lazy library only checks what is needed).
#[test]
fn check_std_checks_the_named_library_file_in_full() {
    let (project, std_dir, cache) = std_edit_fixture("check-std", &[]);
    let std_arg = std_dir.to_str().unwrap();
    let cache_arg = cache.to_str().unwrap();
    let check_std = |target: &str| {
        let output = stitchwort(
            &[
                "--std-dir",
                std_arg,
                "check",
                "--cache-dir",
                cache_arg,
                "--std",
                target,
            ],
            &[],
        );
        (
            output.status.code(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };
    for target in ["Option/Option.sw", "Std.Option.Option", "Option"] {
        let (status, stderr) = check_std(target);
        assert_eq!(status, Some(0), "{target}: {stderr}");
    }
    edit_std(
        &std_dir,
        "Option/Option.sw",
        "Option.map x f1 = Option.map x f2 :=\n  match x with\n    | None => rfl\n    | Some y => Eq.cong Some (ef y)",
        "Option.map x f1 = Option.map x f2 :=\n  match x with\n    | None => rfl\n    | Some y => rfl",
    );
    let (status, stderr) = check_std("Std.Option.Option");
    assert_eq!(status, Some(1), "{stderr}");
    assert!(
        stderr.contains("the library file `std/Option/Option.sw` doesn't check"),
        "{stderr}"
    );
    // A program that doesn't use the file, with the same library, is fine.
    let program = project.join("a.sw");
    std::fs::write(&program, "def x: Nat := 1\n").unwrap();
    let output = stitchwort(
        &[
            "--std-dir",
            std_arg,
            "check",
            "--no-cache",
            program.to_str().unwrap(),
        ],
        &[],
    );
    assert!(output.status.success(), "{}", shown(&output));
    let (status, stderr) = check_std("Nope");
    assert_eq!(status, Some(1), "{stderr}");
    assert!(stderr.contains("E-STD-TARGET"), "{stderr}");
    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&std_dir);
    let _ = std::fs::remove_dir_all(&cache);
}
