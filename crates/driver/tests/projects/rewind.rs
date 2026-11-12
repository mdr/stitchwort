//! Rewinding a session and cancelling a check
//! (docs/proposals/language-server.md, stages 0b and 0c).
//!
//! The differential test: checking, rewinding to a mark and checking again
//! must give exactly what a fresh session gives. The comparison is the
//! check cache's canonical dump of the elaborator (every declaration, every
//! side table, what navigation recorded), every declaration's content hash,
//! the navigation index the editor reads, and the diagnostics. So a table
//! that rewinding forgets, or restores wrongly, shows up as a difference.
//!
//! Three ways of rewinding are compared with a fresh check:
//! - the whole check rewound to a mark before it, and done again;
//! - in a project, each namespace checked, rewound to just before it, and
//!   checked again, before the next (what a language server does when a
//!   namespace is edited);
//! - a check cancelled part way (stage 0c), rewound by
//!   `Session::cancellable`, then done again.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::audit;
use stitchwort_driver::driver::{Session, full_tier, par_map, tier_sample, with_stack};
use stitchwort_driver::live::{LiveProject, Place, Progress};
use stitchwort_driver::nav::index_json;
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::render::render;
use stitchwort_driver::rewind::Cancelled;
use stitchwort_elab::cache::{Key, Store, canonical_dump};
use stitchwort_syntax::{Diagnostic, Severity};

const STACK: usize = 16 * 1024 * 1024;

enum Source {
    File(String, String),
    Project(String, PathBuf),
}

impl Source {
    fn name(&self) -> &str {
        match self {
            Source::File(n, _) | Source::Project(n, _) => n,
        }
    }
}

/// A navigable session. Outside the full tier:
/// - the library's files replay from the test std cache instead of being
///   checked from source in every one of the many sessions here
///   (docs/testing.md, "The test std cache"): the differential is of the
///   program's check;
/// - no counterexample search runs when a theorem fails, but for the
///   examples about it ([`searches`]): a search is much of the time of a
///   rejected example, and what rewinding must restore of one is the same
///   in all of them.
///
/// The full tier checks the library and searches in every session.
fn session(source: &Source) -> Session {
    let mut session = Session::navigable_for_stack(STACK);
    session.use_test_std_cache();
    session.elab.options.no_counterexamples = !searches(source);
    session
}

/// Whether the counterexample search runs when a theorem of `source` fails:
/// always in the full tier, and in the others for the examples named for it.
fn searches(source: &Source) -> bool {
    stitchwort_driver::driver::tier() == stitchwort_driver::driver::Tier::Full
        || source.name().contains("counterexample")
}

/// What a session holds before anything is checked in it ([`outcome`]):
/// every session made by [`session`] starts so, and the dump is a large
/// part of the cost of this file's checks, so it is made once.
fn pristine() -> &'static str {
    static PRISTINE: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    PRISTINE.get_or_init(|| {
        let nothing = Source::File(String::new(), String::new());
        with_stack(STACK, || outcome(&session(&nothing), &Ok(())))
    })
}

/// Checks `source` in `session`: its diagnostics, `Ok` if it has no errors.
fn check(session: &mut Session, source: &Source) -> Result<(), Vec<Diagnostic>> {
    match source {
        Source::File(name, text) => session.load(name, text).map(|_| ()),
        Source::Project(name, path) => session
            .load_project(&DiskFiles { root: path.clone() }, name, &Target::Everything)
            .map(|_| ()),
    }
}

/// Everything a check leaves that anyone reads: the canonical dump, the
/// content hashes, the navigation index and the diagnostics.
fn outcome(session: &Session, result: &Result<(), Vec<Diagnostic>>) -> String {
    let mut out = canonical_dump(&session.elab);
    let g = &session.elab.ev();
    let _op = g
        .machine
        .budget
        .operation(stitchwort_core::Limits::for_stack(STACK));
    for id in 0..g.env.defs().len() {
        out.push_str(&format!("hash def {id} {:?}\n", def_hash(g, DefId(id))));
    }
    for id in 0..g.env.datas().len() {
        out.push_str(&format!("hash data {id} {:?}\n", data_hash(g, DataId(id))));
    }
    drop(_op);
    let diagnostics = match result {
        Ok(()) => session.warnings.clone(),
        Err(ds) => ds.clone(),
    };
    out.push_str(&format!("accepted {}\n", result.is_ok()));
    let errors = diagnostics.iter().any(|d| d.severity == Severity::Error);
    out.push_str(&index_json(session, errors, None, "", &diagnostics));
    out.push('\n');
    for d in &diagnostics {
        out.push_str(&render(&session.sources, d, false));
    }
    out
}

/// The first line where two outcomes differ, with a little context.
fn first_difference(a: &str, b: &str) -> String {
    for (i, (x, y)) in a.lines().zip(b.lines()).enumerate() {
        if x != y {
            return format!("line {i}:\n  fresh:    {x}\n  rewound:  {y}");
        }
    }
    format!(
        "one is a prefix of the other ({} and {} lines)",
        a.lines().count(),
        b.lines().count()
    )
}

fn assert_same(source: &Source, how: &str, fresh: &str, rewound: &str) {
    assert!(
        fresh == rewound,
        "{} ({how}): differs from a fresh check: {}",
        source.name(),
        first_difference(fresh, rewound)
    );
}

/// The outcome of checking `source` in a fresh session.
fn fresh(source: &Source) -> String {
    let mut s = session(source);
    let result = check(&mut s, source);
    outcome(&s, &result)
}

/// Check, rewind to the mark before the check, check again. The rewound
/// session must also be the fresh session again.
fn check_rewind_check(source: &Source, fresh: &str) {
    let mut s = session(source);
    let before = pristine();
    let mark = s.mark();
    let _ = check(&mut s, source);
    s.rewind(&mark);
    assert_same(
        source,
        "rewound to before the check",
        before,
        &outcome(&s, &Ok(())),
    );
    let result = check(&mut s, source);
    assert_same(source, "check, rewind, check", fresh, &outcome(&s, &result));
    // And a mark is good for any number of rewinds.
    s.rewind(&mark);
    let result = check(&mut s, source);
    assert_same(
        source,
        "a second rewind to one mark",
        fresh,
        &outcome(&s, &result),
    );
}

/// Each namespace of a project checked, rewound and checked again.
fn recheck_each_namespace(source: &Source, fresh: &str) {
    let mut s = session(source);
    s.elab.options.recheck_namespaces = true;
    let result = check(&mut s, source);
    assert_same(
        source,
        "each namespace rewound",
        fresh,
        &outcome(&s, &result),
    );
}

/// A check with every cache emptied before every declaration
/// (`Options::clear_caches_per_declaration`): the caches only save work, so
/// the outcome is a fresh check's.
fn check_with_cleared_caches(source: &Source, fresh: &str) {
    let mut s = session(source);
    s.elab.options.clear_caches_per_declaration = true;
    let result = check(&mut s, source);
    assert_same(
        source,
        "caches cleared before every declaration",
        fresh,
        &outcome(&s, &result),
    );
}

/// A check cancelled at the start of its first operation: it says so,
/// leaves the session as it was, and the next check is a fresh one's.
fn cancel_then_check(source: &Source, fresh: &str) {
    let mut s = session(source);
    let before = pristine();
    let flag = s.cancel_flag();
    let mark = s.mark();
    let cancelled = s.cancellable(|s| {
        flag.store(true, Ordering::Relaxed);
        check(s, source)
    });
    match cancelled {
        Err(Cancelled) => {}
        // Nothing was checked (a project whose namespaces form a cycle):
        // nothing to cancel.
        Ok(result) => {
            assert_same(source, "nothing to cancel", fresh, &outcome(&s, &result));
            s.rewind(&mark);
        }
    }
    assert_same(
        source,
        "after a cancelled check",
        before,
        &outcome(&s, &Ok(())),
    );
    let result = s.cancellable(|s| check(s, source));
    let result = result.expect("the flag was cleared");
    assert_same(source, "cancel, then check", fresh, &outcome(&s, &result));
}

fn assert_rewinding_changes_nothing(source: &Source) {
    let fresh = fresh(source);
    check_rewind_check(source, &fresh);
    if matches!(source, Source::Project(..)) {
        recheck_each_namespace(source, &fresh);
    }
    cancel_then_check(source, &fresh);
}

/// The same checks as `assert_rewinding_changes_nothing`, run side by side:
/// for one big source (the AoC project), where the examples' parallelism
/// over sources doesn't help.
fn assert_rewinding_changes_nothing_in_parallel(source: &Source) {
    let fresh = fresh(source);
    let checks: [fn(&Source, &str); 3] = [
        check_rewind_check,
        recheck_each_namespace,
        cancel_then_check,
    ];
    par_map(STACK, &checks, |check| check(source, &fresh));
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
/// full tier, a fixed sample ([`tier_sample`]: in the daily tier every
/// eighth file and every fourth project), and every one with open goals
/// (`goals/`, few; their tables are new) and every one about counterexample
/// searches ([`searches`]).
fn examples() -> Vec<Source> {
    let mut files = Vec::new();
    for dir in ["accept", "extract", "reject", "soundness"] {
        files.extend(example_files(dir));
    }
    let mut projects = example_projects("accept");
    projects.extend(example_projects("reject"));
    let mut goals = example_files("goals");
    goals.extend(example_projects("goals"));
    assert!(!files.is_empty() && !projects.is_empty() && !goals.is_empty());
    let (searching, files): (Vec<_>, Vec<_>) = files.into_iter().partition(searches);
    let mut sources = tier_sample(files, 8);
    sources.extend(tier_sample(projects, 4));
    sources.extend(searching);
    sources.extend(goals);
    sources
}

/// The caches are caches: the examples' sample checked with them emptied
/// before every declaration gives what a fresh check gives.
#[test]
fn emptying_the_caches_changes_nothing_for_the_examples() {
    let sources = examples();
    par_map(STACK, &sources, |source| {
        check_with_cleared_caches(source, &fresh(source));
    });
}

#[test]
fn rewinding_changes_nothing_for_the_examples() {
    let sources = examples();
    par_map(STACK, &sources, assert_rewinding_changes_nothing);
}

fn aoc() -> Source {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    Source::Project("aoc".to_string(), root)
}

#[test]
fn rewinding_changes_nothing_for_the_aoc_project() {
    if !full_tier("rewinding_changes_nothing_for_the_aoc_project") {
        return;
    }
    let source = aoc();
    // The assertions and the timing below are independent: run side by side.
    let parts: [fn(&Source); 2] = [
        assert_rewinding_changes_nothing_in_parallel,
        mark_and_rewind_cost,
    ];
    par_map(STACK, &parts, |part| part(&source));
}

/// `mark_and_rewind_cost` on its own, for `dev/measure-state` (SW-1172):
/// `cargo test --release -p stitchwort-driver --test projects -- --ignored
/// --nocapture rewind::mark_and_rewind_cost_alone`.
#[test]
#[ignore]
fn mark_and_rewind_cost_alone() {
    with_stack(STACK, || mark_and_rewind_cost(&aoc()));
}

/// The resident set of this process, in KB (`ps`), for a rough measure of
/// what a mark holds.
fn rss_kb() -> Option<u64> {
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .ok()?;
    String::from_utf8_lossy(&out.stdout).trim().parse().ok()
}

/// What a mark and a rewind cost after the whole project is checked, and
/// roughly what a mark holds (the resident set's growth over ten marks):
/// `--nocapture` shows it.
fn mark_and_rewind_cost(source: &Source) {
    let mut s = session(source);
    let empty = s.mark();
    let _ = check(&mut s, source);
    let t = std::time::Instant::now();
    let mark = s.mark();
    let marked = t.elapsed();
    let t = std::time::Instant::now();
    s.rewind(&mark);
    let rewound = t.elapsed();
    let ten_marks = |s: &mut Session, what: &str| {
        let before = rss_kb();
        let t = std::time::Instant::now();
        let marks: Vec<_> = (0..10).map(|_| s.mark()).collect();
        let ten = t.elapsed();
        if let (Some(before), Some(after)) = (before, rss_kb()) {
            let more = after.saturating_sub(before);
            eprintln!(
                "aoc with navigation, {what}: ten marks {:.2} ms, resident set {more} KB more ({} KB a mark)",
                ten.as_secs_f64() * 1000.0,
                more / 10
            );
        }
        marks
    };
    let in_namespace = ten_marks(&mut s, "in the last namespace");
    // As a language server marks: once the namespace is left.
    s.elab.leave_namespace();
    let left = ten_marks(&mut s, "the namespace left");
    let t = std::time::Instant::now();
    s.rewind(&empty);
    eprintln!(
        "aoc with navigation: mark {:.2} ms, rewind to it {:.2} ms, rewind to the start {:.2} ms",
        marked.as_secs_f64() * 1000.0,
        rewound.as_secs_f64() * 1000.0,
        t.elapsed().as_secs_f64() * 1000.0
    );
    drop((in_namespace, left));
}

/// Cancelled from another thread at various moments of a check of `aoc`:
/// either it finished first, or it says it was cancelled; either way the
/// next check in the same session gives what a fresh one does. How
/// promptly it stopped is printed (`--nocapture`).
#[test]
fn a_check_cancelled_part_way_rewinds() {
    if !full_tier("a_check_cancelled_part_way_rewinds") {
        return;
    }
    let source = aoc();
    // On a thread of the stack the session is told it has, as the checks
    // below are on `par_map`'s: on libtest's 2 MiB thread, AoC day 22's
    // 2000-deep evaluation overflowed it before the guard could stop it.
    let fresh = with_stack(STACK, || fresh(&source));
    // Each delay is its own session, so they run side by side; true when
    // that check was cancelled.
    let delays = [1u64, 10, 50, 150, 400, 900];
    let was_cancelled = par_map(STACK, &delays, |&delay_ms| {
        let mut cancelled = false;
        {
            let mut s = session(&source);
            let flag = s.cancel_flag();
            let mark = s.mark();
            let setter = flag.clone();
            let (result, set_at, ended) = std::thread::scope(|scope| {
                let setter = scope.spawn(move || {
                    std::thread::sleep(std::time::Duration::from_millis(delay_ms));
                    setter.store(true, Ordering::Relaxed);
                    std::time::Instant::now()
                });
                let result = s.cancellable(|s| check(s, &source));
                let ended = std::time::Instant::now();
                (result, setter.join().unwrap(), ended)
            });
            match result {
                Err(Cancelled) => {
                    cancelled = true;
                    let late = ended.saturating_duration_since(set_at);
                    eprintln!(
                        "flag set at {delay_ms} ms: the check stopped {:.2} ms later",
                        late.as_secs_f64() * 1000.0
                    );
                }
                Ok(_) => {
                    eprintln!("flag set at {delay_ms} ms: the check had finished");
                    s.rewind(&mark);
                }
            }
            let result = s
                .cancellable(|s| check(s, &source))
                .expect("the flag is cleared when a check starts");
            assert_same(
                &source,
                &format!("cancelled at {delay_ms} ms"),
                &fresh,
                &outcome(&s, &result),
            );
        }
        cancelled
    });
    let cancelled = was_cancelled.iter().filter(|c| **c).count();
    assert!(cancelled > 0, "no check was cancelled");
}

// ---- a language server's project, edited and cancelled -----------------

/// An example project's files, by path within it, as a language server
/// reads them.
fn project_files(name: &str) -> BTreeMap<String, String> {
    let root = examples_dir().join("projects/accept").join(name);
    let mut files = BTreeMap::new();
    let mut dirs = vec![root.clone()];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|e| e == "sw" || e == "yaml") {
                let relative = path.strip_prefix(&root).unwrap();
                files.insert(
                    relative.to_string_lossy().to_string(),
                    std::fs::read_to_string(&path).unwrap(),
                );
            }
        }
    }
    files
}

fn live_project(name: &str, files: &BTreeMap<String, String>) -> LiveProject {
    let config = files.get("stitchwort.yaml").cloned();
    let sources = files
        .iter()
        .filter(|(p, _)| p.ends_with(".sw"))
        .map(|(p, t)| (p.clone(), t.clone()))
        .collect();
    LiveProject::new(
        session(&Source::Project(name.to_string(), PathBuf::new())),
        name,
        config,
        sources,
    )
}

/// Steps `live` until everything is checked.
fn finish(live: &mut LiveProject) {
    while let Progress::Checked { .. } = live.step().expect("not cancelled") {}
}

/// What a fresh language server's session holds once it has checked
/// `files`.
fn fresh_live(name: &str, files: &BTreeMap<String, String>) -> String {
    let mut live = live_project(name, files);
    finish(&mut live);
    outcome(&live.session, &Ok(()))
}

/// The project's first namespace's file is edited, checked, edited back and
/// checked, five times (the review's "rewind to one mark twice", at the
/// scale of a project; docs/proposals/elaborator-state.md §4.8.6 item 2):
/// after each check the session is what a fresh one checking the same text
/// holds. Its journal holds the base and a checkpoint per namespace, and
/// what it logs comes back to the same size after each edit back: marks
/// are released, not left open.
fn edit_early_namespace_repeatedly(case: &EditCase, fresh: &[String; 3]) {
    let EditCase { name, early, .. } = case;
    let files = project_files(name);
    let source = Source::Project(name.to_string(), PathBuf::from(name));
    let mut live = live_project(name, &files);
    finish(&mut live);
    let now = outcome(&live.session, &Ok(()));
    assert_same(&source, "first check", &fresh[0], &now);
    let namespaces = live.order().len();
    let first = live.session.elab.journal_stats();
    assert_eq!(
        first.open,
        namespaces + 1,
        "{name}: the base and a mark per namespace"
    );
    for round in 0..5 {
        let edit = 1 + round % 2;
        live.set_text(early, Some(case.text(&files, edit)));
        finish(&mut live);
        assert_same(
            &source,
            &format!("round {round}, edited"),
            &fresh[edit],
            &outcome(&live.session, &Ok(())),
        );
        live.set_text(early, Some(case.text(&files, 0)));
        finish(&mut live);
        assert_same(
            &source,
            &format!("round {round}, edited back"),
            &fresh[0],
            &outcome(&live.session, &Ok(())),
        );
        let now = live.session.elab.journal_stats();
        assert_eq!(
            now.open,
            namespaces + 1,
            "{name}, round {round}: marks left open"
        );
        assert_eq!(
            now.held, first.held,
            "{name}, round {round}: the journal holds more than the project needs"
        );
    }
}

/// An example project, its first namespace's file, and two edits of it
/// (each added at its end).
struct EditCase {
    name: &'static str,
    early: &'static str,
    edits: [&'static str; 2],
}

impl EditCase {
    /// The early file's text: as it is (0) or with an edit (1, 2).
    fn text(&self, files: &BTreeMap<String, String>, edit: usize) -> String {
        let original = &files[self.early];
        match edit {
            0 => original.clone(),
            n => format!("{original}\n{}\n", self.edits[n - 1]),
        }
    }
}

#[test]
fn repeated_edits_of_an_early_namespace_rewind_exactly() {
    let cases = [
        // P.Spec and P.Proofs extend P's `Grid`: rows of an older
        // namespace's that later ones change.
        EditCase {
            name: "extension-visibility",
            early: "src/grid.sw",
            edits: [
                "def Grid.extra (grid: Grid): Nat := grid.width",
                "def broken: Nat := true",
            ],
        },
        // Instances, in the namespace that owns the interface and in
        // another.
        EditCase {
            name: "instance-owners",
            early: "src/geometry.sw",
            edits: [
                "def unit: Nat := 1",
                "instance Area.instBool: Area Bool := { area = b => 1 }",
            ],
        },
    ];
    // Each case's three texts checked fresh, side by side.
    let jobs: Vec<(usize, usize)> = (0..cases.len())
        .flat_map(|c| (0..3).map(move |t| (c, t)))
        .collect();
    let fresh = par_map(STACK, &jobs, |&(c, t)| {
        let case = &cases[c];
        let mut files = project_files(case.name);
        let text = case.text(&files, t);
        files.insert(case.early.to_string(), text);
        fresh_live(case.name, &files)
    });
    let fresh: Vec<[String; 3]> = fresh
        .chunks(3)
        .map(|c| [c[0].clone(), c[1].clone(), c[2].clone()])
        .collect();
    let indices: Vec<usize> = (0..cases.len()).collect();
    par_map(STACK, &indices, |&c| {
        edit_early_namespace_repeatedly(&cases[c], &fresh[c])
    });
}

/// A language server's check cancelled as each namespace begins (the flag
/// set from a check cache's lookup of it, below): it says so, and checking
/// on from there gives what a fresh check gives, with no mark left open.
#[test]
fn a_language_servers_check_cancelled_at_each_namespace_rewinds() {
    let name = "extension-visibility";
    let files = project_files(name);
    let source = Source::Project(name.to_string(), PathBuf::from(name));
    let (fresh, namespaces) = with_stack(STACK, || {
        let mut live = live_project(name, &files);
        finish(&mut live);
        (outcome(&live.session, &Ok(())), live.order().len())
    });
    let points: Vec<usize> = (1..=namespaces).collect();
    par_map(STACK, &points, |&at| {
        let mut live = live_project(name, &files);
        let store = CancellingStore::at_lookup(live.session.cancel_flag(), at);
        live.session.elab.set_check_cache(store.clone());
        let mut cancelled = 0;
        loop {
            match live.step() {
                Ok(Progress::Done) => break,
                Ok(Progress::Checked { .. }) => {}
                Err(_) => cancelled += 1,
            }
        }
        assert_eq!(cancelled, 1, "cancelled once, at namespace {at}");
        assert_same(
            &source,
            &format!("cancelled at namespace {at}"),
            &fresh,
            &outcome(&live.session, &Ok(())),
        );
        let stats = live.session.elab.journal_stats();
        assert_eq!(stats.open, namespaces + 1, "marks left open");
    });
}

/// A check cache that keeps entries in memory and sets the cancellation
/// flag at its `at`th use (a lookup or a write, counting from 1; with
/// `lookups`, only lookups count): so a check is cancelled as a library
/// file or namespace begins to load, nested in another's load or not, or
/// once an entry is written.
struct CancellingStore {
    entries: RefCell<BTreeMap<(String, Key), Vec<u8>>>,
    uses: Cell<usize>,
    at: usize,
    lookups: bool,
    flag: Arc<AtomicBool>,
}

impl CancellingStore {
    fn new(flag: Arc<AtomicBool>, at: usize) -> Rc<CancellingStore> {
        Rc::new(CancellingStore {
            entries: RefCell::default(),
            uses: Cell::new(0),
            at,
            lookups: false,
            flag,
        })
    }

    fn at_lookup(flag: Arc<AtomicBool>, at: usize) -> Rc<CancellingStore> {
        Rc::new(CancellingStore {
            lookups: true,
            ..Rc::into_inner(CancellingStore::new(flag, at)).unwrap()
        })
    }

    fn used(&self) {
        self.uses.set(self.uses.get() + 1);
        if self.uses.get() == self.at {
            self.flag.store(true, Ordering::Relaxed);
        }
    }
}

impl Store for CancellingStore {
    fn compiler(&self) -> &str {
        "rewind.rs"
    }
    fn salt(&self) -> [u8; 16] {
        [7; 16]
    }
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.used();
        self.entries
            .borrow()
            .get(&(unit.to_string(), *key))
            .cloned()
    }
    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        if !self.lookups {
            self.used();
        }
        (self.entries.borrow_mut()).insert((unit.to_string(), *key), entry.to_vec());
    }
}

/// A check with a check cache cancelled at each of its uses of the cache:
/// as a library file or the file begins to load (nested or not) and once an
/// entry is written. Checked again, with the entries written before the
/// cancellation, it gives what a fresh check (with a cache of its own)
/// gives, and the mark `Session::cancellable` took is released.
#[test]
fn a_check_cancelled_at_each_use_of_the_cache_rewinds() {
    let sources = [
        Source::Project(
            "extension-visibility".to_string(),
            examples_dir().join("projects/accept/extension-visibility"),
        ),
        Source::File(
            "accept/parse-digits-messages.sw".to_string(),
            std::fs::read_to_string(examples_dir().join("accept/parse-digits-messages.sw"))
                .unwrap(),
        ),
    ];
    // A fresh check of each, and how many times it uses the cache.
    let fresh: Vec<(String, usize)> = par_map(STACK, &sources, |source| {
        let mut s = session(source);
        let store = CancellingStore::new(Arc::new(AtomicBool::new(false)), 0);
        s.elab.set_check_cache(store.clone());
        let result = check(&mut s, source);
        assert!(result.is_ok(), "{}: {result:?}", source.name());
        let uses = store.uses.get();
        assert!(
            uses > 2,
            "{}: the cache was used {uses} times",
            source.name()
        );
        (outcome(&s, &result), uses)
    });
    // Every use in the full tier; in the others a fixed sample, every third
    // (neighbouring uses are a library file's lookup and its write, or
    // the next file's).
    let points: Vec<(usize, usize)> = (fresh.iter().enumerate())
        .flat_map(|(i, (_, uses))| (1..=*uses).map(move |at| (i, at)))
        .collect();
    let points = tier_sample(points, 3);
    let cancelled = par_map(STACK, &points, |&(i, at)| {
        let source = &sources[i];
        let mut s = session(source);
        let store = CancellingStore::new(s.cancel_flag(), at);
        s.elab.set_check_cache(store.clone());
        let before = s.elab.journal_stats().open;
        let first = s.cancellable(|s| check(s, source));
        assert_eq!(s.elab.journal_stats().open, before, "the mark released");
        let cancelled = first.is_err();
        let result = match first {
            Err(Cancelled) => s.cancellable(|s| check(s, source)).expect("not cancelled"),
            // The flag was set once nothing was left to see it.
            Ok(result) => result,
        };
        assert_same(
            source,
            &format!("cancelled at use {at} of the cache"),
            &fresh[i].0,
            &outcome(&s, &result),
        );
        cancelled
    });
    let cancelled = cancelled.iter().filter(|c| **c).count();
    eprintln!("{cancelled} of {} checks cancelled", points.len());
    assert!(cancelled * 2 > points.len(), "most were cancelled");
}

// ---- editing re-checks what an edit can affect ------------------------------

/// A number no other run has used: the entries it keys are this run's, so
/// the cache's hits and misses are the run's own.
fn nonce() -> String {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
        .to_string()
}

/// A's text, with `nonce` in it: its cache entries are new.
fn order_a(nonce: &str) -> String {
    format!("namespace Order.A\n\ndef base: Nat := {nonce}\n")
}
const ORDER_B: &str = "namespace Order.B\n\nimport Order.A (base)\n\ndef next: Nat := base + 1\n";
const ORDER_C: &str = "namespace Order.C\n\ndef lone: Nat := 7\n";

fn order_files(a: &str) -> BTreeMap<String, String> {
    BTreeMap::from([
        ("src/a.sw".to_string(), a.to_string()),
        ("src/b.sw".to_string(), ORDER_B.to_string()),
        ("src/c.sw".to_string(), ORDER_C.to_string()),
    ])
}

/// The cache the whole test shares, so that `Order.C` can be replayed after
/// an edit rewinds it. Its own directory, rather than the test std cache:
/// [`Session::use_test_std_cache`] sets no cache at all in the full tier,
/// where this test still needs one for the namespaces alone.
fn order_cache(nonce: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("rewind-order-{nonce}"));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn order_project(files: BTreeMap<String, String>, cache: &Path) -> LiveProject {
    let mut session = Session::navigable_for_stack(STACK);
    session.use_check_cache(cache);
    LiveProject::new(
        session,
        "order",
        Some("sources: [src]\n".to_string()),
        files,
    )
}

/// Steps `live` until everything is checked, giving the namespaces it
/// checked, in order.
fn checked_log(live: &mut LiveProject) -> Vec<String> {
    let mut log = Vec::new();
    while let Progress::Checked { .. } = live.step().expect("not cancelled") {
        log.push(live.last_checked().unwrap().to_string());
    }
    log
}

/// A, then B using A, then C using neither. An edit of A rewinds the kernel
/// to before A, which drops C too; A and its user are checked again first
/// (so that their diagnostics come at once), then C, replayed from the
/// check cache, not elaborated. The diagnostics and answers are a fresh
/// check's, and so are the cache's hits.
#[test]
fn an_edit_checks_again_only_what_uses_it() {
    with_stack(STACK, || {
        let nonce = nonce();
        let order_a = order_a(&nonce);
        let cache = order_cache(&nonce);
        let mut live = order_project(order_files(&order_a), &cache);
        assert_eq!(checked_log(&mut live), ["Order.A", "Order.B", "Order.C"]);
        let stats = |live: &LiveProject| live.session.elab.check_cache_stats();

        // The first edit: C goes with the rewind, and comes back from the
        // cache after A and B.
        let before = stats(&live);
        let edited = format!("{order_a}\ndef more: Nat := base + 1\n");
        live.set_text("src/a.sw", Some(edited));
        assert_eq!(checked_log(&mut live), ["Order.A", "Order.B", "Order.C"]);
        let after = stats(&live);
        assert_eq!(
            after.namespace_hits - before.namespace_hits,
            1,
            "C replayed"
        );
        assert_eq!(
            after.namespace_misses - before.namespace_misses,
            2,
            "A and B elaborated"
        );

        // The second, which breaks B.
        let before = stats(&live);
        let broken = order_a.replace("base", "root");
        live.set_text("src/a.sw", Some(broken.clone()));
        assert_eq!(checked_log(&mut live), ["Order.A", "Order.B", "Order.C"]);
        let after = stats(&live);
        assert_eq!(
            after.namespace_hits - before.namespace_hits,
            1,
            "C replayed"
        );
        assert_eq!(
            after.namespace_misses - before.namespace_misses,
            2,
            "A and B elaborated; C not"
        );

        let mut fresh = order_project(order_files(&broken), &cache);
        checked_log(&mut fresh);
        let (now, then) = (live.answers(), fresh.answers());
        assert!(
            now.values().any(|file| !file.diagnostics.is_empty()),
            "B no longer finds `base`"
        );
        assert_eq!(format!("{now:?}"), format!("{then:?}"));

        // And back: the same answers as the first check's.
        live.set_text("src/a.sw", Some(order_a.clone()));
        assert_eq!(checked_log(&mut live), ["Order.A", "Order.B", "Order.C"]);
        let mut first = order_project(order_files(&order_a), &cache);
        checked_log(&mut first);
        let (mut now, mut then) = (live.answers(), first.answers());
        // The library's answers were given with the first call.
        now.retain(|place, _| matches!(place, Place::Program(_)));
        then.retain(|place, _| matches!(place, Place::Program(_)));
        assert_eq!(format!("{now:?}"), format!("{then:?}"));
        let _ = std::fs::remove_dir_all(&cache);
    });
}

// ---- an importer of a namespace with an error ------------------------------

const GAP_A: &str = "namespace Gap.A\n\ndef one: Nat := 1\n\ndef two: Nat := 2\n";
/// `twoIs` uses only `two`; `oneSame` cites `one` without computing it, so
/// it can be checked against a stand-in for `one`; `oneIs` must compute
/// `one`, so it waits for it.
const GAP_B: &str = "namespace Gap.B\n\nimport Gap.A (one, two)\n\n\
    theorem twoIs: two = 2 := rfl\n\n\
    theorem oneSame: one = one := rfl\n\n\
    theorem oneIs: one = 1 := rfl\n";

fn gap_files(a: &str, nonce: &str) -> BTreeMap<String, String> {
    BTreeMap::from([
        (
            "src/a.sw".to_string(),
            format!("{a}\ndef tag: Nat := {nonce}\n"),
        ),
        ("src/b.sw".to_string(), GAP_B.to_string()),
    ])
}

/// How `audit` sees each of `Gap.B`'s theorems.
fn gap_statuses(live: &mut LiveProject) -> BTreeMap<String, audit::Status> {
    let keep = |name: &str| name.starts_with("Gap.B.");
    let theorems = audit::theorems(&live.session.elab.ev(), &keep);
    let options = audit::Options {
        allowed: audit::DEFAULT_ALLOWED
            .iter()
            .map(|a| a.to_string())
            .collect(),
        search: None,
    };
    let mut audits = live.session.audit(&theorems, &options);
    audits.extend(live.session.audit_failed(&keep));
    (audits.into_iter()).map(|a| (a.name, a.status)).collect()
}

/// The codes of the diagnostics answered for `path`.
fn codes(answers: &stitchwort_driver::live::Answers, path: &str) -> Vec<&'static str> {
    let file = &answers[&Place::Program(path.to_string())];
    file.diagnostics.iter().map(|d| d.code).collect()
}

/// In the editor, a namespace that imports one with an error is checked
/// like any user in that namespace's own file
/// (docs/proposals/tests-with-errors.md §3, §6): with a body that doesn't
/// parse or doesn't check, what only cites the broken declaration relies
/// on its stand-in, what computes with it waits, and the rest is checked;
/// with a broken statement or header, everything that uses it waits. A
/// namespace relying on a stand-in is never stored in the check cache.
/// Fixing the error gives back exactly a fresh check's answers.
#[test]
fn an_importer_is_checked_against_a_broken_declarations_stand_in() {
    use audit::Status::{Assuming, Checked, Waiting};
    with_stack(STACK, || {
        let nonce = nonce();
        let cache = order_cache(&format!("gap-{nonce}"));
        let mut live = order_project(gap_files(GAP_A, &nonce), &cache);
        assert_eq!(checked_log(&mut live), ["Gap.A", "Gap.B"]);
        let first = live.answers();
        assert_eq!(codes(&first, "src/b.sw"), Vec::<&str>::new());
        let clean = BTreeMap::from([
            ("Gap.B.oneIs".to_string(), Checked),
            ("Gap.B.oneSame".to_string(), Checked),
            ("Gap.B.twoIs".to_string(), Checked),
        ]);
        assert_eq!(gap_statuses(&mut live), clean);
        let stats = |live: &LiveProject| live.session.elab.check_cache_stats();

        let body_syntax = GAP_A.replace("def one: Nat := 1", "def one: Nat := (1");
        let body_type = GAP_A.replace("def one: Nat := 1", "def one: Nat := \"one\"");
        let statement = GAP_A.replace("def one: Nat := 1", "def one: Nat Nat := 1");
        let header = GAP_A.replace("def one: Nat := 1", "def one: := 1");
        let relying = BTreeMap::from([
            ("Gap.B.oneIs".to_string(), Waiting),
            ("Gap.B.oneSame".to_string(), Assuming),
            ("Gap.B.twoIs".to_string(), Checked),
        ]);
        let waiting = BTreeMap::from([
            ("Gap.B.oneIs".to_string(), Waiting),
            ("Gap.B.oneSame".to_string(), Waiting),
            ("Gap.B.twoIs".to_string(), Checked),
        ]);
        for (what, a, expected) in [
            ("a body with a syntax error", &body_syntax, &relying),
            ("a body with a type error", &body_type, &relying),
            ("a statement with an error", &statement, &waiting),
            ("a header with a syntax error", &header, &waiting),
        ] {
            let before = stats(&live);
            live.set_text("src/a.sw", Some(gap_files(a, &nonce)["src/a.sw"].clone()));
            assert_eq!(checked_log(&mut live), ["Gap.A", "Gap.B"], "{what}");
            let answers = live.answers();
            assert_eq!(codes(&answers, "src/b.sw"), ["E-USES-FAILED"], "{what}");
            assert_eq!(&gap_statuses(&mut live), expected, "{what}");
            // Neither namespace is stored: A has an error, and B relies on
            // it or waits for it, which keeps it out whatever A is.
            let after = stats(&live);
            assert_eq!(after.namespace_written, before.namespace_written, "{what}");
            assert_eq!(
                after.namespace_waiting_on_error, before.namespace_waiting_on_error,
                "{what}: B isn't held back only by A's error"
            );
            // The same as a fresh check of the broken text.
            let mut fresh = order_project(gap_files(a, &nonce), &cache);
            checked_log(&mut fresh);
            let (mut now, mut then) = (answers, fresh.answers());
            now.retain(|place, _| matches!(place, Place::Program(_)));
            then.retain(|place, _| matches!(place, Place::Program(_)));
            assert_eq!(format!("{now:?}"), format!("{then:?}"), "{what}");

            // Fixed: B is back, with nothing left of the stand-in.
            live.set_text(
                "src/a.sw",
                Some(gap_files(GAP_A, &nonce)["src/a.sw"].clone()),
            );
            assert_eq!(checked_log(&mut live), ["Gap.A", "Gap.B"], "{what}, fixed");
            let mut now = live.answers();
            let mut then = first.clone();
            now.retain(|place, _| matches!(place, Place::Program(_)));
            then.retain(|place, _| matches!(place, Place::Program(_)));
            assert_eq!(format!("{now:?}"), format!("{then:?}"), "{what}, fixed");
            assert_eq!(gap_statuses(&mut live), clean, "{what}, fixed");
        }
        let _ = std::fs::remove_dir_all(&cache);
    });
}
