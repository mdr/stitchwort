//! The check cache (docs/proposals/check-cache.md): standard library files
//! (stage 1) and project namespaces (stage 2) loaded from entries written by
//! an earlier run.
//!
//! The differential test (§5.4): a session whose library files and
//! namespaces come from a warm cache must hold exactly what a session that
//! elaborated them holds.
//! The comparison is a canonical dump of the elaborator (every declaration
//! with its terms and flags, every side table, the navigation index) plus
//! the diagnostics, so a table the cache forgets shows up as a difference.
//! Every test here also checks the warm run really loaded from the cache.
//!
//! This is the only test that uses the cache: every other test, the
//! snapshots and the benchmark run without it (D286).

use std::path::{Path, PathBuf};

use stitchwort_driver::driver::{Session, all_tier, par_map, tier_sample, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::render::render;
use stitchwort_elab::JournalStats;
use stitchwort_elab::cache::{Stats, canonical_dump};
use stitchwort_syntax::Diagnostic;

/// The stack every session here runs on, and is told it has
/// ([`Session::for_stack`]): a thread of this size ([`with_stack`] or
/// [`par_map`]), never the test's own thread, whose 2 MiB the session's
/// limits would overrun before stopping it (AoC 2024 day 22's
/// `Nat.iterate 2000` in a test overflowed it).
const STACK: usize = 16 * 1024 * 1024;

/// A new, empty directory for one cache.
fn temp_dir(name: &str) -> PathBuf {
    // The clock alone isn't enough: threads asking at once can read the
    // same time (macOS counts microseconds).
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-check-cache-{name}-{}-{n}-{nanos}",
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
    /// How many of those can't be cached: `Float/Float.sw`, which declares
    /// primitives and binds natives (docs/proposals/float.md, "As built").
    uncacheable: usize,
    /// What the session's journal did and holds at the end.
    journal: JournalStats,
}

/// The library files that can't be cached.
const UNCACHEABLE: &[&str] = &["Float/Float.sw"];

/// Loads `source` in a new session (navigation recorded or not), through
/// the cache in `cache` if there is one.
fn run(source: &Source, nav: bool, cache: Option<&Path>) -> Run {
    with_stack(STACK, || run_here(source, nav, cache, None, None))
}

/// [`run`], with glued evaluation set to `glue` after the session is made
/// (so the core, loaded then, is the same as in every other run).
fn run_with_glue(source: &Source, nav: bool, cache: Option<&Path>, glue: bool) -> Run {
    with_stack(STACK, || run_here(source, nav, cache, Some(glue), None))
}

/// [`run`], on this thread.
/// With `refuse`, the replay of an entry declaring that full path is
/// refused right after its group is admitted
/// (`Elaborator::refuse_replays_after`).
fn run_here(
    source: &Source,
    nav: bool,
    cache: Option<&Path>,
    glue: Option<bool>,
    refuse: Option<&str>,
) -> Run {
    let mut session = if nav {
        Session::navigable_for_stack(STACK)
    } else {
        Session::for_stack(STACK)
    };
    if let Some(path) = refuse {
        session.elab.refuse_replays_after(path);
    }
    if let Some(glue) = glue {
        session.elab.options.glue = glue;
    }
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
        uncacheable: session
            .elab
            .loaded_library_files()
            .iter()
            .filter(|f| UNCACHEABLE.contains(&f.as_str()))
            .count(),
        journal: session.elab.journal_stats(),
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
        cold.stats.uncacheable, fresh.uncacheable,
        "{n}: a library file can't be cached"
    );
    assert!(
        warm.dump == fresh.dump,
        "{n} (nav {nav}): loading from the cache changed the result: {}",
        first_difference(&fresh.dump, &warm.dump)
    );
    assert_eq!(
        (warm.stats.hits, warm.stats.misses),
        (fresh.loaded - fresh.uncacheable, fresh.uncacheable),
        "{n} (nav {nav}): the warm run elaborated a cacheable library file"
    );
    // Every project namespace checked without errors was written, and
    // loaded from the cache the next time; those with errors were
    // elaborated both times.
    assert_eq!(
        cold.stats.namespace_uncacheable, 0,
        "{n}: a namespace can't be cached"
    );
    assert_eq!(
        (warm.stats.namespace_hits, warm.stats.namespace_misses),
        (
            cold.stats.namespace_written,
            cold.stats.namespace_misses - cold.stats.namespace_written
        ),
        "{n} (nav {nav}): the warm run elaborated a namespace it had written"
    );
    assert_eq!(
        (cold.stats.late_misses, warm.stats.late_misses),
        (0, 0),
        "{n} (nav {nav}): a replay failed part way"
    );
    assert_eq!(
        (cold.stats.refused, warm.stats.refused),
        (0, 0),
        "{n} (nav {nav}): the kernel refused a replayed entry"
    );
    if matches!(source, Source::Project(..)) && fresh.dump.contains("\naccepted true\n") {
        assert!(
            warm.stats.namespace_hits > 0,
            "{n} (nav {nav}): no namespace came from the cache"
        );
    }
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
/// all tier, a fixed sample ([`tier_sample`]: every eighth in broad).
fn examples() -> Vec<Source> {
    let mut sources = Vec::new();
    for dir in ["accept", "extract", "reject", "soundness"] {
        sources.extend(example_files(dir));
    }
    sources.extend(example_projects("accept"));
    sources.extend(example_projects("reject"));
    assert!(!sources.is_empty());
    tier_sample(sources, 8)
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

/// Gluing changes the terms elaboration checks (SW-1156: `Std.Nat.divModEq`'s
/// body keeps or unfolds the calls of its inner `Nat` operations), so the
/// key has to keep a glued entry from being replayed into an unglued run.
/// The cold run fills a cache glued; the warm one, unglued, must not load
/// any of it, and must give what a fresh unglued run gives.
#[test]
fn the_cache_keeps_glued_results_from_an_unglued_run() {
    let path = examples_dir().join("accept/adder.sw");
    let source = Source::File(
        "accept/adder.sw".into(),
        std::fs::read_to_string(path).unwrap(),
    );
    let fresh = run_with_glue(&source, false, None, false);
    let dir = temp_dir("glue");
    let cold = run_with_glue(&source, false, Some(&dir), true);
    let warm = run_with_glue(&source, false, Some(&dir), false);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(cold.stats.hits, 0, "a new cache had entries");
    assert!(cold.stats.written > 0, "the glued run wrote nothing");
    assert_eq!(warm.stats.hits, 0, "the unglued run loaded a glued entry");
    assert!(
        warm.dump == fresh.dump,
        "the glued cache changed the unglued result: {}",
        first_difference(&fresh.dump, &warm.dump)
    );
}

/// SW-1072: an example that derives `Ord` over its own `DecEq`, with
/// navigation recorded, round-trips through the cache. Always runs, so the
/// quick tier covers it without the full example sweep.
#[test]
fn the_cache_changes_nothing_for_derive_ord_own_deceq() {
    let path = examples_dir().join("accept/derive-ord-own-deceq.sw");
    let source = Source::File(
        "accept/derive-ord-own-deceq.sw".into(),
        std::fs::read_to_string(&path).unwrap(),
    );
    par_map(STACK, &[source], |source| {
        assert_cache_changes_nothing(source, true);
    });
}

/// Opaque definitions and their `unfolding` lists are replayed through the
/// kernel (docs/proposals/opaque-definitions.md), whatever the sample.
#[test]
fn the_cache_replays_opaque_definitions() {
    let project = Source::Project(
        "opaque-across-namespaces".into(),
        examples_dir().join("projects/accept/opaque-across-namespaces"),
    );
    assert_cache_changes_nothing(&project, false);
    assert_cache_changes_nothing(&project, true);
}

/// Readings (docs/proposals/bool-as-proposition.md §5) are replayed with
/// the namespace that declares them, and read the same from another,
/// whatever the sample.
#[test]
fn the_cache_replays_readings() {
    let project = Source::Project(
        "readings-across-namespaces".into(),
        examples_dir().join("projects/accept/readings-across-namespaces"),
    );
    assert_cache_changes_nothing(&project, false);
}

/// Functions a namespace adds to another namespace's type are replayed with
/// the keys they stand for (docs/proposals/extending-types.md), whatever
/// the sample.
#[test]
fn the_cache_replays_extensions() {
    let project = Source::Project(
        "extension-visibility".into(),
        examples_dir().join("projects/accept/extension-visibility"),
    );
    assert_cache_changes_nothing(&project, false);
    assert_cache_changes_nothing(&project, true);
}

/// `P.Spec` adds a function to `P`'s type, but its `import P` brings the
/// namespace whose own error says `P` can't see the addition. `P.Spec` is
/// checked and not written (SW-2951); the differential test must not read
/// that as an entry that can't be encoded.
#[test]
fn the_cache_changes_nothing_for_extension_in_owner() {
    let project = Source::Project(
        "extension-in-owner".into(),
        examples_dir().join("projects/reject/extension-in-owner"),
    );
    assert_cache_changes_nothing(&project, true);
}

/// Parameter defaults are replayed from the cache: the defaulting table of
/// each definition, and calls in a namespace checked afresh against a
/// cached one that leave a defaulted parameter out; with navigation, the
/// defaults each call used, for hover.
#[test]
fn the_cache_replays_parameter_defaults() {
    let source = examples_dir().join("projects/accept/param-defaults-across-namespaces");
    let project = Source::Project("param-defaults-across-namespaces".into(), source.clone());
    assert_cache_changes_nothing(&project, false);
    assert_cache_changes_nothing(&project, true);

    let copy = temp_dir("param-defaults-project");
    std::fs::create_dir_all(copy.join("src")).unwrap();
    for file in ["stitchwort.yaml", "src/layout.sw", "src/report.sw"] {
        std::fs::copy(source.join(file), copy.join(file)).unwrap();
    }
    let cache = temp_dir("param-defaults-cache");
    let copied = Source::Project("param-defaults-copy".into(), copy.clone());
    let cold = run(&copied, false, Some(&cache));
    assert!(cold.dump.contains("\naccepted true\n"), "{}", cold.dump);
    let report = copy.join("src/report.sw");
    let mut text = std::fs::read_to_string(&report).unwrap();
    text.push_str("\ntheorem fourColumns: columns 4 = 7 := rfl\n");
    std::fs::write(&report, text).unwrap();
    let warm = run(&copied, false, Some(&cache));
    let _ = std::fs::remove_dir_all(&copy);
    let _ = std::fs::remove_dir_all(&cache);
    assert!(warm.dump.contains("\naccepted true\n"), "{}", warm.dump);
    assert!(
        warm.stats.namespace_hits >= 1,
        "`Layout` wasn't loaded from the cache"
    );
    assert!(warm.dump.contains("\nparam defaults "));
    assert!(warm.dump.contains(" ParamDefaults {"));
}

/// An interface's dictionary has no record eta (D2502): a mark the
/// elaborator sets, which the kernel can't recompute, so the entry keeps
/// it. Replayed from the cache, the dictionary must neither get eta back
/// (`dictEta` is rejected warm as it is fresh) nor hash differently.
#[test]
fn the_cache_keeps_an_interface_without_eta() {
    let project = temp_dir("no-eta-project");
    std::fs::create_dir_all(project.join("src")).unwrap();
    std::fs::write(project.join("stitchwort.yaml"), "# Sizes and Use\n").unwrap();
    std::fs::write(
        project.join("src/sizes.sw"),
        "namespace Sizes\n\ninterface Sized (k: Type) =\n  { size: k → Nat }\n",
    )
    .unwrap();
    std::fs::write(
        project.join("src/use.sw"),
        "namespace Use\n\nimport Sizes (Sized)\n\n\
         theorem dictEta (s: Sized Nat): s = { size = s.size } := rfl\n",
    )
    .unwrap();
    let source = Source::Project("no-eta".into(), project.clone());
    let fresh = run(&source, false, None);
    assert!(
        fresh.dump.contains("\naccepted false\n") && fresh.dump.contains("E-REFL"),
        "{}",
        fresh.dump
    );
    assert!(fresh.dump.contains(" record true eta false no_eta true "));
    assert_cache_changes_nothing(&source, false);

    // The dictionary's hash, computed afresh rather than taken from the
    // entry that was replayed.
    let sized_hash = |cache: Option<&Path>| {
        with_stack(STACK, || {
            let mut session = Session::for_stack(STACK);
            if let Some(dir) = cache {
                session.use_check_cache(dir);
            }
            let _ = session.load_project(
                &DiskFiles {
                    root: project.clone(),
                },
                "no-eta",
                &Target::Everything,
            );
            let hits = session.elab.check_cache_stats().namespace_hits;
            let ev = session.elab.ev();
            ev.caches.hashes.borrow_mut().clear();
            let sized = (0..ev.env.datas().len())
                .map(stitchwort_core::DataId)
                .find(|&d| ev.env.data(d).path().to_string() == "Sizes.Sized")
                .expect("Sizes.Sized is declared");
            (stitchwort_core::hash::data_hash(&ev, sized).unwrap(), hits)
        })
    };
    let cache = temp_dir("no-eta-cache");
    let (cold, _) = sized_hash(Some(&cache));
    let (warm, hits) = sized_hash(Some(&cache));
    let _ = std::fs::remove_dir_all(&project);
    let _ = std::fs::remove_dir_all(&cache);
    assert_eq!(hits, 1, "`Sizes` wasn't loaded from the cache");
    assert_eq!(cold, warm, "the dictionary hashes differently warm");
}

/// `@[tailrec]` is a flag of the definition, kept in the entry: a namespace
/// loaded from the cache has it on the definition, local `go` included (the
/// dump lists it, so the warm dump must equal the fresh one).
#[test]
fn the_cache_replays_tailrec() {
    let project = Source::Project(
        "tailrec-namespace".into(),
        examples_dir().join("projects/accept/tailrec-namespace"),
    );
    assert_cache_changes_nothing(&project, false);
    let fresh = run(&project, false, None);
    assert!(fresh.dump.contains(" tailrec true "), "{}", fresh.dump);
}

#[test]
fn the_cache_changes_nothing_for_the_aoc_project() {
    if !all_tier("the_cache_changes_nothing_for_the_aoc_project") {
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let aoc = Source::Project("aoc".to_string(), root);
    // With and without navigation recorded: independent, so side by side.
    par_map(STACK, &[false, true], |&nav| {
        assert_cache_changes_nothing(&aoc, nav);
    });
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

/// A library file that runs out of resources is marked loaded (its error
/// is the program's answer, E-RESOURCE), but no entry is written for it:
/// a later run elaborates it again and runs out again.
#[test]
fn a_file_that_runs_out_of_resources_is_not_written() {
    let dir = temp_dir("resource");
    let attempt = || {
        with_stack(STACK, || {
            let mut session = Session::for_stack(STACK);
            session.elab.options.limits.work = 20_000;
            session.use_check_cache(&dir);
            let result = session.elab.load_all_libraries();
            (
                result,
                session.elab.check_cache_stats(),
                session.elab.loaded_library_files().len(),
            )
        })
    };
    let (result, cold, loaded) = attempt();
    let errors = result.expect_err("the limit is too low for the library");
    assert!(errors.iter().any(|d| d.code == "E-RESOURCE"), "{errors:?}");
    assert_eq!(cold.uncacheable, 0);
    assert!(cold.written > 0, "some files load within the limit");
    assert_eq!(
        cold.written + 1,
        loaded,
        "every file but the one that ran out"
    );
    let (result, warm, _) = attempt();
    assert!(result.is_err_and(|ds| ds.iter().any(|d| d.code == "E-RESOURCE")));
    assert_eq!((warm.hits, warm.misses), (cold.written, 1));
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- Project namespaces (stage 2) -------------------------------------

/// A project in a new folder: `files` are (path in it, text).
fn temp_project(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let dir = temp_dir(name);
    write_file(&dir, "stitchwort.yaml", "sources: [src]\n");
    for (path, text) in files {
        write_file(&dir, path, text);
    }
    dir
}

fn write_file(dir: &Path, path: &str, text: &str) {
    let full = dir.join(path);
    std::fs::create_dir_all(full.parent().unwrap()).unwrap();
    std::fs::write(full, text).unwrap();
}

/// A project of three namespaces: `B` uses `A`, and `C` uses neither.
const ABC: &[(&str, &str)] = &[
    (
        "src/A.sw",
        "namespace A\n\ndef one: Nat := 1\n\ntest \"one\" := one == 1\n",
    ),
    (
        "src/B.sw",
        "namespace B\n\nimport A (one)\n\ndef two: Nat := one + one\n",
    ),
    ("src/C.sw", "namespace C\n\ndef three: Nat := 3\n"),
];

/// Loads the project at `dir`, fresh and through the cache in `cache`, and
/// checks they agree; the cache's statistics.
fn fresh_and_cached(dir: &Path, cache: &Path) -> Stats {
    let source = Source::Project("p".to_string(), dir.to_path_buf());
    let fresh = run(&source, true, None);
    let cached = run(&source, true, Some(cache));
    assert!(
        cached.dump == fresh.dump,
        "the cache changed the result: {}",
        first_difference(&fresh.dump, &cached.dump)
    );
    cached.stats
}

#[test]
fn an_edit_re_elaborates_the_namespace_and_what_uses_it() {
    let dir = temp_project("merkle", ABC);
    let cache = temp_dir("merkle-cache");
    let cold = fresh_and_cached(&dir, &cache);
    assert_eq!((cold.namespace_hits, cold.namespace_written), (0, 3));
    let warm = fresh_and_cached(&dir, &cache);
    assert_eq!((warm.namespace_hits, warm.namespace_misses), (3, 0));
    // A comment in `A`: `A` and `B`, which uses it, are elaborated again.
    write_file(&dir, "src/A.sw", &format!("-- a comment\n{}", ABC[0].1));
    let edited = fresh_and_cached(&dir, &cache);
    assert_eq!((edited.namespace_hits, edited.namespace_misses), (1, 2));
    // A comment in `B`: only `B`.
    write_file(&dir, "src/B.sw", &format!("-- a comment\n{}", ABC[1].1));
    let edited = fresh_and_cached(&dir, &cache);
    assert_eq!((edited.namespace_hits, edited.namespace_misses), (2, 1));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// `A` declares a test and its reading, `B` takes a fact apart through it,
/// `C` uses neither.
const READING: &[(&str, &str)] = &[
    (
        "src/A.sw",
        "namespace A\n\ntype Small (n: Nat): Prop = { below: n < 10 }\n\n\
         def small (n: Nat): Bool := n < 10\n\n\
         @[reading]\ntheorem smallReads (n: Nat): small n ↔ Small n := \
         { forward = h => { below = h }, backward = s => s.below }\n",
    ),
    (
        "src/B.sw",
        "namespace B\n\nimport A (small)\n\n\
         theorem below (n: Nat) (h: small n): n < 10 :=\n  match h with\n    | { below } => below\n",
    ),
    ("src/C.sw", "namespace C\n\ndef three: Nat := 3\n"),
];

/// A reading is declared with its test, so a namespace that reads through
/// it uses the namespace that declares it, whose key changes with it: an
/// edited reading checks again what reads through it.
#[test]
fn an_edited_reading_re_checks_what_reads_through_it() {
    let dir = temp_project("reading", READING);
    let cache = temp_dir("reading-cache");
    let cold = fresh_and_cached(&dir, &cache);
    assert_eq!((cold.namespace_hits, cold.namespace_written), (0, 3));
    let warm = fresh_and_cached(&dir, &cache);
    assert_eq!((warm.namespace_hits, warm.namespace_misses), (3, 0));
    // A comment in `B`: it is checked again, reading through `A`'s
    // reading as replayed from the cache.
    write_file(&dir, "src/B.sw", &format!("-- a comment\n{}", READING[1].1));
    let edited = fresh_and_cached(&dir, &cache);
    assert_eq!((edited.namespace_hits, edited.namespace_misses), (2, 1));
    // The reading no longer gives a record, so `B`'s record pattern fails.
    write_file(
        &dir,
        "src/A.sw",
        "namespace A\n\ndef small (n: Nat): Bool := n < 10\n\n\
         @[reading]\ntheorem smallReads (n: Nat): small n ↔ n < 10 := \
         { forward = h => h, backward = h => h }\n",
    );
    let edited = fresh_and_cached(&dir, &cache);
    assert_eq!((edited.namespace_hits, edited.namespace_misses), (1, 2));
    let source = Source::Project("p".to_string(), dir.clone());
    let again = run(&source, true, Some(&cache));
    assert!(
        again.dump.contains("accepted false") && again.dump.contains("B.sw"),
        "`B` should fail through the edited reading:\n{}",
        again
            .dump
            .lines()
            .rev()
            .take(20)
            .collect::<Vec<_>>()
            .join("\n")
    );
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

#[test]
fn a_namespace_with_errors_is_not_written() {
    let dir = temp_project("errors", ABC);
    write_file(&dir, "src/C.sw", "namespace C\n\ndef three: Nat := True\n");
    let cache = temp_dir("errors-cache");
    let cold = fresh_and_cached(&dir, &cache);
    assert_eq!((cold.namespace_written, cold.namespace_uncacheable), (2, 0));
    let warm = fresh_and_cached(&dir, &cache);
    assert_eq!((warm.namespace_hits, warm.namespace_misses), (2, 1));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// A namespace that uses one with an error is checked, but its entry isn't
/// written: its key would be keyed to the broken source, and writing it
/// would delete the entry the healthy source finds again (SW-2951).
#[test]
fn removing_an_error_finds_its_importers_earlier_entries() {
    let dir = temp_project("errors-removed", ABC);
    let cache = temp_dir("errors-removed-cache");
    let cold = fresh_and_cached(&dir, &cache);
    assert_eq!((cold.namespace_written, cold.namespace_uncacheable), (3, 0));
    // `A` gets an error in `bad`, which `B` doesn't use: `B` still checks,
    // with `A`'s new key, and is the one that must not be written.
    write_file(
        &dir,
        "src/A.sw",
        "namespace A\n\ndef one: Nat := 1\n\ndef bad: Nat := True\n\ntest \"one\" := one == 1\n",
    );
    let broken = fresh_and_cached(&dir, &cache);
    assert_eq!((broken.namespace_hits, broken.namespace_written), (1, 0));
    assert_eq!(broken.namespace_uncacheable, 0);
    assert_eq!(broken.namespace_waiting_on_error, 1);
    write_file(&dir, "src/A.sw", ABC[0].1);
    let fixed = fresh_and_cached(&dir, &cache);
    assert_eq!((fixed.namespace_hits, fixed.namespace_misses), (3, 0));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

#[test]
fn a_change_to_an_included_file_is_a_miss() {
    let dir = temp_project(
        "include",
        &[
            (
                "src/Day.sw",
                "namespace Day\n\ndef input: Text := include \"../input.txt\"\n\n\
                 test \"input\" := input == \"1\\n\"\n",
            ),
            ("input.txt", "1\n"),
        ],
    );
    let cache = temp_dir("include-cache");
    fresh_and_cached(&dir, &cache);
    assert_eq!(fresh_and_cached(&dir, &cache).namespace_hits, 1);
    write_file(&dir, "input.txt", "2\n");
    let changed = fresh_and_cached(&dir, &cache);
    assert_eq!((changed.namespace_hits, changed.namespace_misses), (0, 1));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// The configuration and the list of namespaces are in every key.
#[test]
fn a_new_namespace_or_configuration_is_a_miss() {
    let dir = temp_project("config", ABC);
    let cache = temp_dir("config-cache");
    fresh_and_cached(&dir, &cache);
    write_file(&dir, "src/D.sw", "namespace D\n");
    let added = fresh_and_cached(&dir, &cache);
    assert_eq!((added.namespace_hits, added.namespace_misses), (0, 4));
    write_file(&dir, "stitchwort.yaml", "# the same\nsources: [src]\n");
    let configured = fresh_and_cached(&dir, &cache);
    assert_eq!(configured.namespace_hits, 0);
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

// ---- Different targets, one cache (SW-255) ------------------------------

/// `A` uses a library file, and so does `B`, which `B.Tests` uses. A whole
/// project check loads `std/Fin/Fin.sw` for `A`, before `B`; `B` on its
/// own (`run B.main`) has to load it itself.
const SPLIT: &[(&str, &str)] = &[
    (
        "src/A.sw",
        "namespace A\nimport Std (Fin)\n\ndef two: Fin 3 := Fin.ofNat 2\n",
    ),
    (
        "src/B/B.sw",
        "namespace B\nimport Std (Fin, IO)\n\ndef three: Fin 4 := Fin.ofNat 3\n\n\
         def main(): {IO} () := IO.print \"three is ${three}\"\n",
    ),
    (
        "src/B/Tests/Tests.sw",
        "namespace B.Tests\nimport B (three)\nimport Std (Fin)\n\n\
         test \"three\" := Fin.toNat three == 3\n",
    ),
];

fn target(names: &[&str]) -> Target {
    if names.is_empty() {
        Target::Everything
    } else {
        Target::Namespaces(names.iter().map(|n| n.to_string()).collect())
    }
}

/// Loads `target` of the project at `dir` (navigation recorded), through
/// the cache in `cache` if there is one, with every namespace replay made
/// to fail part way if `fail_late`; and the namespaces it checked.
fn run_target(
    dir: &Path,
    target: &Target,
    cache: Option<&Path>,
    fail_late: bool,
) -> (Run, Vec<String>) {
    run_target_recording(dir, target, cache, fail_late, false)
}

/// [`run_target`], also recording the type of every expression if `exprs`.
fn run_target_recording(
    dir: &Path,
    target: &Target,
    cache: Option<&Path>,
    fail_late: bool,
    exprs: bool,
) -> (Run, Vec<String>) {
    with_stack(STACK, || {
        run_target_here(dir, target, cache, fail_late, exprs, None)
    })
}

/// [`run_target_recording`], on this thread.
fn run_target_here(
    dir: &Path,
    target: &Target,
    cache: Option<&Path>,
    fail_late: bool,
    exprs: bool,
    refuse: Option<&str>,
) -> (Run, Vec<String>) {
    let mut session = Session::navigable_for_stack(STACK);
    if let Some(path) = refuse {
        session.elab.refuse_replays_after(path);
    }
    if exprs {
        session.elab.enable_expression_types();
    }
    if let Some(cache) = cache {
        session.use_check_cache(cache);
    }
    if fail_late {
        session.elab.fail_namespace_replays_late();
    }
    let files = DiskFiles {
        root: dir.to_path_buf(),
    };
    let result = session.load_project(&files, "p", target);
    let mut dump = canonical_dump(&session.elab);
    let (diagnostics, checked) = match &result {
        Ok(loaded) => (session.warnings.clone(), loaded.checked.clone()),
        Err(ds) => (ds.clone(), Vec::new()),
    };
    dump.push_str(&format!("accepted {}\n", result.is_ok()));
    for d in &diagnostics {
        dump.push_str(&render(&session.sources, d, false));
    }
    let run = Run {
        dump,
        stats: session.elab.check_cache_stats(),
        loaded: session.elab.loaded_library_files().len(),
        uncacheable: 0,
        journal: session.elab.journal_stats(),
    };
    (run, checked)
}

/// Fills a new cache by loading `writer` of the project at `dir`, then
/// loads `reader` from it and checks that gives what loading `reader`
/// without a cache gives, with no replay failing part way and every
/// namespace both checked loaded from the cache.
fn assert_targets_share(dir: &Path, writer: &[&str], reader: &[&str]) {
    let cache = temp_dir("targets-cache");
    let (_, written) = run_target(dir, &target(writer), Some(&cache), false);
    let (fresh, checked) = run_target(dir, &target(reader), None, false);
    let (cached, _) = run_target(dir, &target(reader), Some(&cache), false);
    let _ = std::fs::remove_dir_all(&cache);
    let what = format!("{writer:?} then {reader:?}");
    assert!(
        fresh.dump.contains("\naccepted true\n"),
        "{what}: {}",
        fresh.dump
    );
    assert!(
        cached.dump == fresh.dump,
        "{what}: the cache changed the result: {}",
        first_difference(&fresh.dump, &cached.dump)
    );
    assert_eq!(
        cached.stats.late_misses, 0,
        "{what}: a replay failed part way"
    );
    assert_eq!(
        cached.stats.refused, 0,
        "{what}: the kernel refused a replayed entry"
    );
    let shared = checked.iter().filter(|n| written.contains(n)).count();
    assert_eq!(
        cached.stats.namespace_hits, shared,
        "{what}: not every namespace both checked came from the cache"
    );
}

/// What one command writes, another reads: `check` then `run`, `run` then
/// `check`, and so on. A namespace's entry mustn't depend on which library
/// files happened to be loaded when it was written.
#[test]
fn different_targets_share_one_cache() {
    let dir = temp_project("targets", SPLIT);
    for (writer, reader) in [
        (&[][..], &["B"][..]),
        (&[], &["B.Tests"]),
        (&["B"], &[]),
        (&["B.Tests"], &["B"]),
        (&["A"], &["B"]),
        (&["B"], &["A", "B.Tests"]),
    ] {
        assert_targets_share(&dir, writer, reader);
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// `aoc`'s namespaces each on their own (as `run` and the editor's save
/// load them), from a cache the whole project wrote.
#[test]
fn aocs_namespaces_load_on_their_own_from_the_whole_projects_cache() {
    if !all_tier("aocs_namespaces_load_on_their_own_from_the_whole_projects_cache") {
        return;
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let cache = temp_dir("aoc-targets-cache");
    let (_, written) = run_target(&root, &Target::Everything, Some(&cache), false);
    assert!(written.len() > 10, "{written:?}");
    par_map(STACK, &written, |ns| {
        let reader = Target::Namespaces(vec![ns.clone()]);
        let (fresh, checked) = run_target(&root, &reader, None, false);
        let (cached, _) = run_target(&root, &reader, Some(&cache), false);
        assert!(
            cached.dump == fresh.dump,
            "{ns}: the cache changed the result: {}",
            first_difference(&fresh.dump, &cached.dump)
        );
        assert_eq!(
            (cached.stats.namespace_hits, cached.stats.late_misses),
            (checked.len(), 0),
            "{ns}: not every namespace came from the cache"
        );
    });
    let _ = std::fs::remove_dir_all(&cache);
}

/// A replay that fails part way (a late miss) leaves what it began for
/// the namespace's elaboration to finish: the result is the same as
/// without a cache, and not, say, every name declared twice.
#[test]
fn a_replay_that_fails_part_way_gives_the_same_result() {
    let dir = temp_project("late", SPLIT);
    let cache = temp_dir("late-cache");
    for names in [&[][..], &["B"], &["B.Tests"]] {
        let reader = target(names);
        let (fresh, checked) = run_target(&dir, &reader, None, false);
        // Written, then replayed, failing part way.
        run_target(&dir, &reader, Some(&cache), false);
        let (late, _) = run_target(&dir, &reader, Some(&cache), true);
        assert!(
            late.dump == fresh.dump,
            "{names:?}: a late miss changed the result: {}",
            first_difference(&fresh.dump, &late.dump)
        );
        assert_eq!(
            (late.stats.late_misses, late.stats.namespace_hits),
            (checked.len(), 0),
            "{names:?}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// SW-1925: a namespace's entry the kernel refuses after its first group
/// is undone (the undo is checked at once, against the kernel at the
/// mark: `admit_replayed`), and the namespace elaborated in what is left
/// gives what a fresh check gives.
#[test]
fn a_namespace_entry_refused_part_way_gives_the_same_result() {
    let dir = temp_project("refused", SPLIT);
    let cache = temp_dir("refused-cache");
    let (fresh, _) = run_target(&dir, &target(&[]), None, false);
    run_target(&dir, &target(&[]), Some(&cache), false);
    let (refused, _) = with_stack(STACK, || {
        run_target_here(
            &dir,
            &target(&[]),
            Some(&cache),
            false,
            false,
            Some("A.two"),
        )
    });
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
    assert!(
        refused.dump == fresh.dump,
        "a refused namespace replay changed the result: {}",
        first_difference(&fresh.dump, &refused.dump)
    );
    assert_eq!(
        (refused.stats.refused, refused.stats.late_misses),
        (1, 1),
        "A's entry wasn't refused (and nothing else was)"
    );
}

/// The standard library with `Float/Float.sw` cut before its primitives,
/// which keep it out of the cache, so that its entry, with the Float
/// built-ins it binds, can be written and replayed; the rest goes to
/// `Float/Rest.sw`. In a new directory.
fn std_with_cacheable_float() -> PathBuf {
    fn copy(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).unwrap();
        for entry in std::fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let target = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copy(&entry.path(), &target);
            } else {
                std::fs::copy(entry.path(), &target).unwrap();
            }
        }
    }
    let std = temp_dir("float-std");
    copy(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std"),
        &std,
    );
    let float = std.join("Float/Float.sw");
    let text = std::fs::read_to_string(&float).unwrap();
    let cut = text
        .find("\n-- The other rounding operations")
        .expect("Float.sw's primitives, after `Float.sub`");
    std::fs::write(&float, &text[..cut + 1]).unwrap();
    // The library must still declare every Float built-in, so the rest of
    // the file, primitives included, moves to a file of its own, which this
    // test never loads. Its instances become plain definitions: an instance
    // must be declared in its type's file.
    let rest = text[cut + 1..].replace("\ninstance ", "\ndef ");
    std::fs::write(std.join("Float/Rest.sw"), rest).unwrap();
    std
}

/// SW-1925 (the elab review's F1): a library entry the kernel refuses after
/// it has bound `Float` and `Float.add`'s native is undone completely, the
/// Float bindings included. The undo is checked when it is done, against
/// the kernel at the mark (`admit_replayed`): checking afterwards would
/// pass anyway, since elaborating the file binds the same ids again.
///
/// It reads its own copy of the library, which a process reads once: it
/// needs a process of its own, as nextest gives every test.
#[test]
fn a_refused_library_entry_takes_back_its_float_bindings() {
    let std = std_with_cacheable_float();
    stitchwort_elab::use_std_dir(&std)
        .expect("the library was read already: run this test in a process of its own (nextest)");
    let cache = temp_dir("refused-float-cache");
    let source = Source::File(
        "main.sw".to_string(),
        "import Std (Float)\n\ndef x: Float := Float.add Float.nan Float.nan\n".to_string(),
    );
    let fresh = run(&source, false, None);
    let cold = run(&source, false, Some(&cache));
    let refused = with_stack(STACK, || {
        run_here(&source, false, Some(&cache), None, Some("Std.Float.add"))
    });
    let _ = std::fs::remove_dir_all(&std);
    let _ = std::fs::remove_dir_all(&cache);
    assert!(
        fresh.dump.contains("\naccepted true\n") && fresh.dump.contains("float Native("),
        "Float.sw didn't load and bind its natives: {}",
        fresh.dump
    );
    assert_eq!(
        (cold.stats.uncacheable, cold.stats.written),
        (0, cold.loaded),
        "the cut Float.sw still can't be cached"
    );
    assert!(
        refused.dump == fresh.dump,
        "a refused replay changed the result: {}",
        first_difference(&fresh.dump, &refused.dump)
    );
    assert_eq!(refused.stats.refused, 1, "Float.sw's entry wasn't refused");
}

/// The types of expressions (for hovering over a selection) are in the
/// cache's entries: a namespace loaded from it records what checking it did.
#[test]
fn expression_types_come_back_from_the_cache() {
    let dir = temp_project("expression-types", SPLIT);
    let cache = temp_dir("expression-types-cache");
    let (written, _) = run_target_recording(&dir, &target(&[]), Some(&cache), false, true);
    let (cached, _) = run_target_recording(&dir, &target(&[]), Some(&cache), false, true);
    let (fresh, _) = run_target_recording(&dir, &target(&[]), None, false, true);
    let _ = std::fs::remove_dir_all(&cache);
    assert!(
        fresh.dump.contains("\nnav expr "),
        "no expression types recorded"
    );
    assert!(
        cached.stats.namespace_hits > 0,
        "nothing came from the cache"
    );
    assert!(
        cached.dump == fresh.dump && written.dump == fresh.dump,
        "the cache changed the result: {}",
        first_difference(&fresh.dump, &cached.dump)
    );
}

/// A4 (docs/proposals/map-equality.md §14.3): the five quotient forms
/// round-trip through the cache. The dump holds every term with its forms'
/// erasure flags, so a form written or read back wrongly is a difference.
#[test]
fn quotient_forms_round_trip_through_the_cache() {
    let source = "namespace Quotients\n\n\
                  def AllTrue (x: Bool) (y: Bool): Prop := Unit\n\
                  def Q: Type := Quot Bool AllTrue\n\
                  theorem same: (Quot.mk False: Q) = Quot.mk True := Quot.sound Trivial\n\
                  def zeroOf (q: Q): Nat := Quot.lift (b => 0) (x y r => rfl) q\n\
                  theorem alwaysZero (q: Q): zeroOf q = 0 :=\n  \
                  Quot.ind [p := q => zeroOf q = 0] (b => rfl) q\n\
                  theorem zeroOfTrue: zeroOf (Quot.mk True) = 0 := rfl\n";
    let dir = temp_project("quotients", &[("src/Quotients.sw", source)]);
    let project = Source::Project("p".to_string(), dir.clone());
    let fresh = run(&project, true, None);
    assert!(
        fresh.dump.contains("\naccepted true\n"),
        "not accepted:\n{}",
        fresh.dump
    );
    for form in stitchwort_core::QuotForm::ALL {
        assert!(
            fresh.dump.contains(&format!("({} ", form.name())),
            "no `{}` in the dump",
            form.name()
        );
    }
    let cache = temp_dir("quotients-cache");
    let cold = fresh_and_cached(&dir, &cache);
    assert_eq!(cold.namespace_written, 1);
    let warm = fresh_and_cached(&dir, &cache);
    assert_eq!((warm.namespace_hits, warm.namespace_misses), (1, 0));
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

// ---- Attributes (docs/proposals/attributes.md §6.5, §9.2) ---------------

/// `Shapes` declares attributed types, the field `centerX` with the key
/// `key` in JavaScript; `App` imports them and exports functions of them.
fn attributed_project(key: &str) -> Vec<(&'static str, String)> {
    vec![
        (
            "src/Shapes.sw",
            format!(
                "namespace Shapes\n\n\
                 @[js.tag \"type\"]\n\
                 type Shape =\n  \
                 | @[js.name \"DOT\"] Dot\n  \
                 | @[js.name \"CIRCLE\"] Circle (radius: Nat) (@[js.name \"{key}\"] centerX: Nat)\n\n\
                 type Drawing = {{ @[js.name \"type\"] kind: Text, shapes: List Shape }}\n\n\
                 @[js.enum]\n\
                 type Palette =\n  \
                 | @[js.name \"{key}-red\"] Red\n  \
                 | Green\n"
            ),
        ),
        (
            "src/App.sw",
            "namespace App\n\nimport Shapes (Shape, Drawing, Palette)\n\n\
             export def next: Palette -> Palette\n  \
             | Palette.Red => Palette.Green\n  \
             | Palette.Green => Palette.Red\n\n\
             export def grow: Shape -> Shape\n  \
             | Shape.Dot => Shape.Dot\n  \
             | Shape.Circle r x => Shape.Circle (r + 1) x\n\n\
             export def count (d: Drawing): Nat := d.shapes.length\n"
                .to_string(),
        ),
    ]
}

/// What a build of `App` gives: the module and its declarations, the
/// logical hashes of every declaration of the project's two namespaces, and
/// what the cache did.
fn build_app(dir: &Path, cache: Option<&Path>) -> (stitchwort_js::Output, Vec<String>, Stats) {
    with_stack(STACK, || build_app_here(dir, cache))
}

/// [`build_app`], on this thread.
fn build_app_here(dir: &Path, cache: Option<&Path>) -> (stitchwort_js::Output, Vec<String>, Stats) {
    let mut session = Session::for_stack(STACK);
    if let Some(dir) = cache {
        session.use_check_cache(dir);
    }
    let files = DiskFiles {
        root: dir.to_path_buf(),
    };
    if let Err(ds) = session.load_project(&files, "p", &Target::Everything) {
        let rendered: String = ds
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect();
        panic!("the project doesn't check:\n{rendered}");
    }
    let output = session
        .extract_namespace("App")
        .expect("extraction succeeds");
    let g = &session.elab.ev();
    let ours = |path: &str| path.contains("Shapes.") || path.contains("App.");
    let mut hashes = Vec::new();
    for d in (0..g.env.datas().len()).map(stitchwort_core::DataId) {
        if ours(g.data(d).path()) {
            let hash = stitchwort_core::hash::data_hash(g, d).expect("hashes");
            hashes.push(format!(
                "{} {}",
                g.data(d).path(),
                hash.expect("checked").hex()
            ));
        }
    }
    for id in (0..g.env.defs().len()).map(stitchwort_core::DefId) {
        if ours(g.def(id).path()) {
            let hash = stitchwort_core::hash::def_hash(g, id).expect("hashes");
            hashes.push(format!("{} {:?}", g.def(id).path(), hash.map(|h| h.hex())));
        }
    }
    (output, hashes, session.elab.check_cache_stats())
}

/// The metadata-only edit (docs/proposals/attributes.md §9.2): `js_repr`
/// isn't in any hash, so it travels in the declaring namespace's entry. A
/// `js.name` changed in an imported namespace reaches the generated code and
/// declarations whether that namespace is elaborated or loaded from the
/// cache, and no logical hash changes.
#[test]
fn an_attributes_only_edit_in_an_imported_namespace_reaches_the_javascript() {
    let files = attributed_project("center_x");
    let files: Vec<(&str, &str)> = files.iter().map(|(p, t)| (*p, t.as_str())).collect();
    let dir = temp_project("attributes", &files);
    let cache = temp_dir("attributes-cache");
    let (fresh, hashes, _) = build_app(&dir, None);
    assert!(
        fresh.dts.contains("readonly center_x: bigint"),
        "{}",
        fresh.dts
    );
    // A string union's strings travel the same way (`js_repr`'s `string_enum`).
    assert!(
        fresh
            .dts
            .contains("export type Palette = \"center_x-red\" | \"Green\";"),
        "{}",
        fresh.dts
    );
    let (cold, _, _) = build_app(&dir, Some(&cache));
    let (warm, warm_hashes, stats) = build_app(&dir, Some(&cache));
    assert!(
        stats.namespace_hits > 0,
        "`Shapes` didn't come from the cache"
    );
    for (what, out) in [("cold", &cold), ("warm", &warm)] {
        assert_eq!(out.js, fresh.js, "the {what} build's module differs");
        assert_eq!(out.dts, fresh.dts, "the {what} build's declarations differ");
    }
    assert_eq!(warm_hashes, hashes);

    // Only `Shapes`'s representation changes.
    let edited = attributed_project("cx");
    write_file(&dir, "src/Shapes.sw", &edited[0].1);
    let (fresh_edited, edited_hashes, _) = build_app(&dir, None);
    let (cold_edited, _, _) = build_app(&dir, Some(&cache));
    let (warm_edited, warm_edited_hashes, stats) = build_app(&dir, Some(&cache));
    assert!(
        stats.namespace_hits > 0,
        "`Shapes` didn't come from the cache"
    );
    assert!(
        fresh_edited.dts.contains("readonly cx: bigint") && !fresh_edited.dts.contains("center_x"),
        "{}",
        fresh_edited.dts
    );
    assert!(
        fresh_edited
            .dts
            .contains("export type Palette = \"cx-red\" | \"Green\";"),
        "{}",
        fresh_edited.dts
    );
    assert!(
        fresh_edited
            .js
            .contains("[\"cx\", NAT, false, \"centerX\"]"),
        "{}",
        fresh_edited.js
    );
    for (what, out) in [("cold", &cold_edited), ("warm", &warm_edited)] {
        assert_eq!(out.js, fresh_edited.js, "the {what} build's module differs");
        assert_eq!(
            out.dts, fresh_edited.dts,
            "the {what} build's declarations differ"
        );
    }
    // Attributes aren't part of logical hashes (D598).
    assert_eq!(edited_hashes, hashes);
    assert_eq!(warm_edited_hashes, hashes);
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// SW-386: a lemma about one `{ c | id = x }` applies to a separately
/// written, identical update in another namespace, cold and warm.
#[test]
fn identical_updates_are_equal_cold_and_warm() {
    let dir = temp_project(
        "update-identity",
        &[
            (
                "src/Shapes.sw",
                "namespace Shapes\n\n\
                 type Shape =\n  | Dot (ref: Nat) (id: Nat)\n  | Circle (ref: Nat) (id: Nat) (radius: Nat)\n\n\
                 def setId (c: Shape) (x: Nat): Shape := { c | id = x }\n\n\
                 theorem idRead (c: Shape) (x: Nat): ({ c | id = x }).id = x :=\n  \
                 match c with\n    | Dot _ _ => rfl\n    | Circle _ _ _ => rfl\n",
            ),
            (
                "src/User.sw",
                "namespace User\n\nimport Shapes (Shape, setId, idRead)\n\n\
                 def setIdAgain (c: Shape) (x: Nat): Shape := { c | id = x }\n\n\
                 theorem same (c: Shape) (x: Nat): setId c x = setIdAgain c x := rfl\n\n\
                 theorem read (c: Shape) (x: Nat): (setIdAgain c x).id = x := idRead c x\n",
            ),
        ],
    );
    let source = Source::Project("p".to_string(), dir.clone());
    assert!(run(&source, false, None).dump.contains("\naccepted true\n"));
    assert_cache_changes_nothing(&source, false);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A record of propositions that nothing decides gets no derived decision
/// (SW-1015), and no half-made instance either: its namespace is cached
/// like any other.
#[test]
fn a_record_that_cannot_be_decided_is_cached() {
    let dir = temp_project(
        "undecidable-record",
        &[(
            "src/R.sw",
            "namespace R\n\n\
             type Both (p: Prop) (n: Nat): Prop = { first: p, second: n = n }\n\n\
             def one: Nat := 1\n",
        )],
    );
    assert_targets_share(&dir, &[], &["R"]);
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- Side tables kept by the elaborator (SW-1128) -----------------------

/// Fills a new cache from the project at `dir`, edits `src/B.sw` (so that
/// `A` is replayed and `B` elaborated again), and checks that loading the
/// edited project through the cache gives what loading it fresh does,
/// diagnostics included. The cached run's dump.
fn assert_replay_changes_nothing(dir: &Path) -> String {
    let cache = temp_dir("replay-cache");
    let source = Source::Project("p".to_string(), dir.to_path_buf());
    let cold = run(&source, false, Some(&cache));
    assert_eq!(cold.stats.namespace_hits, 0);
    let b = std::fs::read_to_string(dir.join("src/B.sw")).unwrap();
    write_file(dir, "src/B.sw", &format!("-- edited\n{b}"));
    let fresh = run(&source, false, None);
    let warm = run(&source, false, Some(&cache));
    let _ = std::fs::remove_dir_all(&cache);
    assert_eq!(
        (warm.stats.namespace_hits, warm.stats.namespace_misses),
        (1, 1),
        "`A` was replayed and `B` elaborated"
    );
    assert!(
        warm.dump == fresh.dump,
        "replaying a namespace changed the result: {}",
        first_difference(&fresh.dump, &warm.dump)
    );
    warm.dump
}

#[test]
fn a_replayed_type_keeps_why_finite_isnt_derived() {
    let dir = temp_project(
        "no-finite",
        &[
            ("src/A.sw", "namespace A\n\ntype Wide =\n  | Mk (n: Nat)\n"),
            (
                "src/B.sw",
                "namespace B\n\nimport A (Wide)\n\ndef every: List Wide := Finite.all\n",
            ),
        ],
    );
    let fresh = run(&Source::Project("p".to_string(), dir.clone()), false, None);
    assert!(
        fresh.dump.contains("isn't derived for `A.Wide`"),
        "the fresh run has the note:\n{}",
        fresh.dump
    );
    let warm = assert_replay_changes_nothing(&dir);
    assert!(warm.contains("isn't derived for `A.Wide`"), "{warm}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_replayed_record_keeps_why_no_decision_is_derived() {
    let dir = temp_project(
        "no-decide",
        &[
            (
                "src/A.sw",
                "namespace A\n\ntype Dep: Prop = { n: Nat, same: n = n }\n",
            ),
            (
                "src/B.sw",
                "namespace B\n\nimport A (Dep)\n\ndef isDep: Bool := if h: Dep then True else False\n",
            ),
        ],
    );
    let fresh = run(&Source::Project("p".to_string(), dir.clone()), false, None);
    assert!(
        fresh.dump.contains("has no derived decision"),
        "the fresh run has the note:\n{}",
        fresh.dump
    );
    let warm = assert_replay_changes_nothing(&dir);
    assert!(warm.contains("has no derived decision"), "{warm}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_replayed_container_keeps_its_generated_all() {
    let dir = temp_project(
        "generated-all",
        &[
            (
                "src/A.sw",
                "namespace A\n\ntype Box (a: Type): Type =\n  | MkBox (x: a)\n\n\
                 type Tree: Type =\n  | Node (inside: Box Tree)\n  | Leaf\n\n\
                 def Tree.size: Tree → Nat\n  | Leaf => 0\n  | Node (MkBox t) => Succ (Tree.size t)\n",
            ),
            (
                "src/B.sw",
                "namespace B\n\nimport A (Box)\n\n\
                 type Other: Type =\n  | Wrap (inside: Box Other)\n  | Stop\n\n\
                 def Other.size: Other → Nat\n  | Stop => 0\n  | Wrap (MkBox t) => Succ (Other.size t)\n",
            ),
        ],
    );
    let fresh = run(&Source::Project("p".to_string(), dir.clone()), false, None);
    assert!(fresh.dump.contains("\naccepted true\n"), "{}", fresh.dump);
    // `B` reuses `A.Box.All`, not a private `%Box%All` of its own.
    let warm = assert_replay_changes_nothing(&dir);
    assert!(!warm.contains("%Box%All"), "B generated its own All");
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- Tables the canonical dump and the entries lacked (SW-1135, SW-1140) --

#[test]
fn a_replayed_namespace_keeps_the_equations_it_asked_the_library_for() {
    let dir = temp_project(
        "equations-done",
        &[
            (
                "src/A.sw",
                "namespace A\n\nimport Std (List)\n\ntheorem mapNil (f: Nat → Nat): List.map Nil f = Nil := List.map.eq1 f\n",
            ),
            ("src/B.sw", "namespace B\n\ndef three: Nat := 3\n"),
        ],
    );
    let fresh = run(&Source::Project("p".to_string(), dir.clone()), false, None);
    assert!(fresh.dump.contains("\naccepted true\n"), "{}", fresh.dump);
    // `B` doesn't ask again, so only the entry can say that `A` did.
    let warm = assert_replay_changes_nothing(&dir);
    assert!(warm.contains("equations_done Std.List.map"), "{warm}");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn a_replayed_function_keeps_needing_its_row_total() {
    let dir = temp_project(
        "total-rows",
        &[
            (
                "src/A.sw",
                "namespace A\n\nimport Std (Fail)\nimport Std.Effect (Effects)\n\n\
                 type Job (e: Effects): Type =\n  | MkJob (run: () → {Fail | e} Nat)\n\n\
                 def runJob (job: Job e): {e} Nat := Fail.orElse 0 (Job.run job)\n\n\
                 def viaJob (f: () → {Fail | e} Nat): {e} Nat := runJob (MkJob f)\n",
            ),
            (
                "src/B.sw",
                "namespace B\n\nimport A (viaJob)\nimport Std (Fail)\n\n\
                 def spin (n: Nat): {Fail, Partial} Nat := spin (n + 1)\n\n\
                 def partialJob(): {Partial} Nat := viaJob (() => spin 0)\n",
            ),
        ],
    );
    let fresh = run(&Source::Project("p".to_string(), dir.clone()), false, None);
    assert!(
        fresh.dump.contains("takes only total callbacks"),
        "the fresh run has the note:\n{}",
        fresh.dump
    );
    let warm = assert_replay_changes_nothing(&dir);
    assert!(warm.contains("takes only total callbacks"), "{warm}");
    let _ = std::fs::remove_dir_all(&dir);
}

// ---- Entries from write-sets (docs/proposals/elaborator-state.md §4.8.3) --

/// The entry of the namespace named `unit` (`ns.A`) in a cache directory.
fn entry_of(cache: &Path, unit: &str) -> PathBuf {
    let found: Vec<PathBuf> = (entries(cache).into_iter())
        .filter(|p| {
            let name = p.file_name().unwrap().to_str().unwrap();
            name.contains(&format!("-{unit}-")) || name.contains(&format!("-{unit}+"))
        })
        .collect();
    assert_eq!(found.len(), 1, "one entry for {unit}: {found:?}");
    found.into_iter().next().unwrap()
}

/// A copy of the cache directory `from`, without the entries of `drop`.
fn copy_cache(from: &Path, name: &str, drop: &[&str]) -> PathBuf {
    let to = temp_dir(name);
    std::fs::create_dir_all(to.join("check")).unwrap();
    std::fs::copy(from.join("check/header"), to.join("check/header")).unwrap();
    let dropped: Vec<PathBuf> = drop.iter().map(|u| entry_of(from, u)).collect();
    for e in entries(from) {
        if !dropped.contains(&e) {
            std::fs::copy(&e, to.join("check").join(e.file_name().unwrap())).unwrap();
        }
    }
    to
}

/// A namespace that loads a library file inside it writes the same entry
/// whether the file comes from the cache, is elaborated because the cache
/// hasn't got it, or is elaborated because its entry is corrupt: the file's
/// load, replayed or elaborated, is its own unit's write-set, not the
/// namespace's (§4.8.6 item 2). Each run is as a fresh one.
#[test]
fn a_namespace_writes_the_same_entry_whether_its_library_files_hit_or_miss() {
    let dir = temp_project(
        "nested",
        &[
            (
                "src/A.sw",
                "namespace A\nimport Std (Fin)\n\ndef two: Fin 3 := Fin.ofNat 2\n\n\
                 test \"two\" := Fin.toNat two == 2\n",
            ),
            (
                "src/B.sw",
                "namespace B\nimport A (two)\nimport Std (Fin)\n\ndef again: Fin 3 := two\n",
            ),
        ],
    );
    let source = Source::Project("p".to_string(), dir.clone());
    let fresh = run(&source, true, None);
    let check = |cache: &Path, what: &str| {
        let r = run(&source, true, Some(cache));
        assert!(
            r.dump == fresh.dump,
            "{what}: the cache changed the result: {}",
            first_difference(&fresh.dump, &r.dump)
        );
        (r.stats, std::fs::read(entry_of(cache, "ns.A")).unwrap())
    };
    let cold = temp_dir("nested-cold");
    let (stats, written) = check(&cold, "no entries");
    assert_eq!((stats.hits, stats.namespace_written), (0, 2));
    // The library's entries, not the namespaces'.
    let hits = copy_cache(&cold, "nested-hits", &["ns.A", "ns.B"]);
    let (stats, with_hits) = check(&hits, "the library files' entries");
    assert!(stats.hits > 0 && stats.written == 0, "{stats:?}");
    assert_eq!(stats.namespace_misses, 2);
    assert!(
        with_hits == written,
        "the entry changed when its library files hit"
    );
    // The same, with the entry of the file `A` loads corrupt.
    let corrupt = copy_cache(&cold, "nested-corrupt", &["ns.A", "ns.B"]);
    let fin = entry_of(&corrupt, "std.Fin.Fin");
    let mut bytes = std::fs::read(&fin).unwrap();
    let middle = bytes.len() / 2;
    bytes[middle] ^= 0xff;
    std::fs::write(&fin, bytes).unwrap();
    let (stats, with_corrupt) = check(&corrupt, "a corrupt library entry");
    assert!(stats.misses > 0 && stats.written > 0, "{stats:?}");
    assert!(
        with_corrupt == written,
        "the entry changed when a library file missed"
    );
    for d in [&dir, &cold, &hits, &corrupt] {
        let _ = std::fs::remove_dir_all(d);
    }
}

/// A check with the cache logs one unit's writes at a time: each unit's
/// transaction is all that is open, and when it ends the log is dropped
/// (§4.8.2), so a command-line check holds no log of the whole project.
#[test]
fn a_check_with_the_cache_holds_no_log_between_units() {
    let dir = temp_project("journal", ABC);
    let cache = temp_dir("journal-cache");
    let source = Source::Project("p".to_string(), dir.clone());
    for run in [
        run(&source, false, Some(&cache)),
        run(&source, false, Some(&cache)),
    ] {
        let j = run.journal;
        assert_eq!((j.open, j.held, j.checkpoints), (0, 0, 0), "{j:?}");
        assert!(j.transactions >= 3, "a transaction per namespace: {j:?}");
        assert!(j.peak_entries < j.entries, "{j:?}");
    }
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// A namespace's instance and extension of an older namespace's type, and
/// its names, come back from its entry usable: a namespace elaborated after
/// its replay uses them as after a fresh check (§4.8.6 item 2).
#[test]
fn a_replayed_namespaces_instances_and_extensions_are_usable() {
    let dir = temp_project(
        "replay-then-depend",
        &[
            (
                "src/A.sw",
                "namespace A\n\ninterface Size (a: Type) =\n  { size: a → Nat }\n\n\
                 type Box = { width: Nat }\n\n\
                 instance Box.instSize: Size Box :=\n  { size = b => b.width }\n",
            ),
            (
                "src/B.sw",
                "namespace B\n\nimport A (Box, Size)\n\n\
                 def Box.double (box: Box): Nat := box.width * 2\n\n\
                 def sample: Box := { width = 3 }\n\n\
                 test \"instance\" := Size.size sample == 3\n\
                 test \"extension\" := sample.double == 6\n",
            ),
            (
                "src/C.sw",
                "namespace C\n\nimport A (Box, Size)\nimport B (..)\n\n\
                 def bigger: Box := { width = sample.double }\n\n\
                 test \"both\" := Size.size bigger == 6\n\
                 test \"full name\" := B.Box.double bigger == 12\n",
            ),
        ],
    );
    let source = Source::Project("p".to_string(), dir.clone());
    for (edit, replayed) in [("src/C.sw", 2), ("src/B.sw", 1)] {
        let cache = temp_dir("replay-then-depend-cache");
        let cold = run(&source, false, Some(&cache));
        assert_eq!(cold.stats.namespace_written, 3);
        let text = std::fs::read_to_string(dir.join(edit)).unwrap();
        write_file(&dir, edit, &format!("-- edited\n{text}"));
        let fresh = run(&source, false, None);
        let warm = run(&source, false, Some(&cache));
        let _ = std::fs::remove_dir_all(&cache);
        assert_eq!(
            (warm.stats.namespace_hits, warm.stats.namespace_misses),
            (replayed, 3 - replayed),
            "{edit}"
        );
        assert!(
            warm.dump == fresh.dump,
            "{edit}: replaying changed the result: {}",
            first_difference(&fresh.dump, &warm.dump)
        );
        assert!(fresh.dump.contains("accepted true"), "{}", fresh.dump);
    }
    let _ = std::fs::remove_dir_all(&dir);
}
