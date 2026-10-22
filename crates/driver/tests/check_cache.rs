//! The check cache (docs/proposals/check-cache.md), stage 1: standard
//! library files loaded from entries written by an earlier run.
//!
//! The differential test (§5.4): a session whose library files come from a
//! warm cache must hold exactly what a session that elaborated them holds.
//! The comparison is a canonical dump of the elaborator (every declaration
//! with its terms and flags, every side table, the navigation index) plus
//! the diagnostics, so a table the cache forgets shows up as a difference.
//! Every test here also checks the warm run really loaded from the cache.
//!
//! This is the only test that uses the cache: every other test, the
//! snapshots and the benchmark run without it (D286).

use std::path::{Path, PathBuf};

use stitchwort_driver::driver::{Session, par_map, slow_tier, slow_tier_on};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::render::render;
use stitchwort_elab::cache::{Stats, canonical_dump};
use stitchwort_syntax::Diagnostic;

const STACK: usize = 16 * 1024 * 1024;

/// A new, empty directory for one cache.
fn temp_dir(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-check-cache-{name}-{}-{nanos}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

enum Source {
    File(String, String),
    Project(String, PathBuf),
    /// Every library file, loaded up front.
    Library,
}

impl Source {
    fn name(&self) -> &str {
        match self {
            Source::File(n, _) | Source::Project(n, _) => n,
            Source::Library => "the whole library",
        }
    }
}

/// What a run gave: the dump, the cache's statistics, and the library
/// files it loaded.
struct Run {
    dump: String,
    stats: Stats,
    loaded: usize,
}

/// Loads `source` in a new session (navigation recorded or not), through
/// the cache in `cache` if there is one.
fn run(source: &Source, nav: bool, cache: Option<&Path>) -> Run {
    let mut session = if nav {
        Session::navigable_for_stack(STACK)
    } else {
        Session::for_stack(STACK)
    };
    if let Some(dir) = cache {
        session.use_check_cache(dir);
    }
    let result: Result<(), Vec<Diagnostic>> = match source {
        Source::File(name, text) => session.load(name, text).map(|_| ()),
        Source::Project(name, path) => session
            .load_project(&DiskFiles { root: path.clone() }, name, &Target::Everything)
            .map(|_| ()),
        Source::Library => session.elab.load_all_libraries(),
    };
    let mut dump = canonical_dump(&session.elab);
    let diagnostics = match &result {
        Ok(()) => session.warnings.clone(),
        Err(ds) => ds.clone(),
    };
    dump.push_str(&format!("accepted {}\n", result.is_ok()));
    for d in &diagnostics {
        dump.push_str(&render(&session.sources, d, false));
    }
    Run {
        dump,
        stats: session.elab.check_cache_stats(),
        loaded: session.elab.loaded_library_files().len(),
    }
}

/// The first line where two dumps differ, with a little context.
fn first_difference(a: &str, b: &str) -> String {
    for (i, (x, y)) in a.lines().zip(b.lines()).enumerate() {
        if x != y {
            return format!("line {i}:\n  fresh: {x}\n  warm:  {y}");
        }
    }
    format!(
        "one is a prefix of the other ({} and {} lines)",
        a.lines().count(),
        b.lines().count()
    )
}

/// Loads `source` fresh, then twice through a new cache (cold, then warm),
/// and checks the warm run loaded every library file from the cache and
/// gave the same dump as the fresh one. So did the cold one, which wrote
/// the entries.
fn assert_cache_changes_nothing(source: &Source, nav: bool) {
    let n = source.name();
    let dir = temp_dir("diff");
    let fresh = run(source, nav, None);
    let cold = run(source, nav, Some(&dir));
    let warm = run(source, nav, Some(&dir));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        cold.dump == fresh.dump,
        "{n} (nav {nav}): writing the cache changed the result: {}",
        first_difference(&fresh.dump, &cold.dump)
    );
    assert_eq!(cold.stats.hits, 0, "{n}: a new cache had entries");
    assert_eq!(
        cold.stats.written + cold.stats.uncacheable,
        fresh.loaded,
        "{n}: every library file loaded was written or found uncacheable"
    );
    assert_eq!(
        cold.stats.uncacheable, 0,
        "{n}: a library file can't be cached"
    );
    assert!(
        warm.dump == fresh.dump,
        "{n} (nav {nav}): loading from the cache changed the result: {}",
        first_difference(&fresh.dump, &warm.dump)
    );
    assert_eq!(
        (warm.stats.hits, warm.stats.misses),
        (fresh.loaded, 0),
        "{n} (nav {nav}): the warm run elaborated a library file"
    );
}

#[test]
fn the_whole_library_loads_the_same_from_the_cache() {
    assert_cache_changes_nothing(&Source::Library, false);
}

#[test]
fn the_whole_library_loads_the_same_from_the_cache_with_navigation() {
    assert_cache_changes_nothing(&Source::Library, true);
}

fn examples_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

fn example_files(dir: &str) -> Vec<Source> {
    let Ok(entries) = std::fs::read_dir(examples_dir().join(dir)) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|p| {
            Source::File(
                format!("{dir}/{}", p.file_name().unwrap().to_string_lossy()),
                std::fs::read_to_string(&p).unwrap(),
            )
        })
        .collect()
}

fn example_projects(dir: &str) -> Vec<Source> {
    let root = examples_dir().join("projects").join(dir);
    let Ok(entries) = std::fs::read_dir(&root) else {
        return Vec::new();
    };
    let mut dirs: Vec<PathBuf> = entries
        .map(|e| e.unwrap().path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    dirs.into_iter()
        .map(|p| Source::Project(p.file_name().unwrap().to_string_lossy().to_string(), p))
        .collect()
}

/// Every example: files and projects, accepted and rejected. Outside the
/// slow tier, every eighth (a fixed sample).
fn examples() -> Vec<Source> {
    let mut sources = Vec::new();
    for dir in ["accept", "extract", "reject", "soundness"] {
        sources.extend(example_files(dir));
    }
    sources.extend(example_projects("accept"));
    sources.extend(example_projects("reject"));
    assert!(!sources.is_empty());
    if slow_tier_on() {
        sources
    } else {
        sources.into_iter().step_by(8).collect()
    }
}

/// With navigation recorded, which covers more of what an entry holds; the
/// whole library without it is checked above.
#[test]
fn the_cache_changes_nothing_for_the_examples() {
    let sources = examples();
    par_map(STACK, &sources, |source| {
        assert_cache_changes_nothing(source, true);
    });
}

#[test]
fn the_cache_changes_nothing_for_the_aoc_project() {
    if !slow_tier("the_cache_changes_nothing_for_the_aoc_project") {
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let aoc = Source::Project("aoc".to_string(), root);
    for nav in [false, true] {
        assert_cache_changes_nothing(&aoc, nav);
    }
}

/// A program that loads a few library files.
fn small_program() -> Source {
    let path = examples_dir().join("accept/day2-chunks.sw");
    Source::File(
        "day2-chunks.sw".to_string(),
        std::fs::read_to_string(path).unwrap(),
    )
}

/// The entries in a cache directory.
fn entries(dir: &Path) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = std::fs::read_dir(dir.join("check"))
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.file_name().is_some_and(|n| n != "header"))
        .collect();
    out.sort();
    out
}

#[test]
fn a_corrupt_entry_is_a_miss_and_is_rewritten() {
    let source = small_program();
    let dir = temp_dir("corrupt");
    let fresh = run(&source, false, None);
    run(&source, false, Some(&dir));
    let files = entries(&dir);
    assert!(!files.is_empty());
    // One byte changed in the middle of each entry.
    let mut originals = Vec::new();
    for path in &files {
        let mut bytes = std::fs::read(path).unwrap();
        originals.push(bytes.clone());
        let at = bytes.len() / 2;
        bytes[at] ^= 0x55;
        std::fs::write(path, bytes).unwrap();
    }
    let again = run(&source, false, Some(&dir));
    assert_eq!(again.dump, fresh.dump);
    assert_eq!(
        (again.stats.hits, again.stats.misses, again.stats.written),
        (0, files.len(), files.len())
    );
    for (path, original) in files.iter().zip(&originals) {
        assert_eq!(
            &std::fs::read(path).unwrap(),
            original,
            "rewritten as it was"
        );
    }
    // Cut short, the same.
    for path in &files {
        let bytes = std::fs::read(path).unwrap();
        std::fs::write(path, &bytes[..bytes.len() / 3]).unwrap();
    }
    let again = run(&source, false, Some(&dir));
    assert_eq!(again.dump, fresh.dump);
    assert_eq!(again.stats.hits, 0);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn entries_from_another_cache_directory_are_misses() {
    let source = small_program();
    let (a, b) = (temp_dir("salt-a"), temp_dir("salt-b"));
    run(&source, false, Some(&a));
    run(&source, false, Some(&b));
    // The entries of `a` copied over `b`'s: same names, other salt.
    for path in entries(&a) {
        std::fs::copy(&path, b.join("check").join(path.file_name().unwrap())).unwrap();
    }
    let again = run(&source, false, Some(&b));
    assert_eq!(again.stats.hits, 0);
    assert_eq!(again.stats.misses, again.loaded);
    // And `b` rewrote them, so they load now.
    let warm = run(&source, false, Some(&b));
    assert_eq!(warm.stats.hits, warm.loaded);
    let _ = std::fs::remove_dir_all(&a);
    let _ = std::fs::remove_dir_all(&b);
}

#[test]
fn an_entry_under_another_key_is_a_miss() {
    let source = small_program();
    let dir = temp_dir("key");
    run(&source, false, Some(&dir));
    let files = entries(&dir);
    assert!(files.len() >= 2, "{files:?}");
    // Each entry's bytes under the next one's name.
    let bytes: Vec<Vec<u8>> = files.iter().map(|p| std::fs::read(p).unwrap()).collect();
    for (i, path) in files.iter().enumerate() {
        std::fs::write(path, &bytes[(i + 1) % bytes.len()]).unwrap();
    }
    let again = run(&source, false, Some(&dir));
    assert_eq!(again.stats.hits, 0);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn navigation_has_entries_of_its_own() {
    let source = small_program();
    let dir = temp_dir("nav");
    let plain = run(&source, false, Some(&dir));
    let nav = run(&source, true, Some(&dir));
    assert_eq!(nav.stats.hits, 0, "an entry without navigation was used");
    assert_eq!(nav.stats.written, plain.stats.written);
    // Both kinds are kept.
    assert_eq!(run(&source, false, Some(&dir)).stats.misses, 0);
    assert_eq!(run(&source, true, Some(&dir)).stats.misses, 0);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn writing_an_entry_deletes_the_units_older_ones() {
    let source = small_program();
    let dir = temp_dir("evict");
    run(&source, false, Some(&dir));
    let files = entries(&dir);
    // An older entry of the same unit and build: another key.
    let name = files[0].file_name().unwrap().to_string_lossy().to_string();
    let (unit, _key) = name.rsplit_once('-').unwrap();
    let older = dir.join("check").join(format!("{unit}-{}", "0".repeat(64)));
    std::fs::write(&older, b"old").unwrap();
    // And an entry of another build, new and old.
    let other_new = dir.join("check").join("000000000000000000000000-std.X-00");
    std::fs::write(&other_new, b"other").unwrap();
    std::fs::remove_file(&files[0]).unwrap();
    let again = run(&source, false, Some(&dir));
    assert_eq!(again.stats.written, 1);
    assert!(!older.exists(), "the unit's older entry is gone");
    assert!(
        other_new.exists(),
        "another build's entry is kept for a day"
    );
    let _ = std::fs::remove_dir_all(&dir);
}
