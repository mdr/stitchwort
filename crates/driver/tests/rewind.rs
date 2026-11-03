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
use stitchwort_driver::driver::{Session, full_tier, par_map, tier_sample, with_stack};
use stitchwort_driver::live::{LiveProject, Progress};
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

fn session() -> Session {
    Session::navigable_for_stack(STACK)
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
    let g = &session.elab.globals;
    let _op = g
        .budget
        .operation(stitchwort_core::Limits::for_stack(STACK));
    for id in 0..g.defs.len() {
        out.push_str(&format!("hash def {id} {:?}\n", def_hash(g, DefId(id))));
    }
    for id in 0..g.datas.len() {
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
    let mut s = session();
    let result = check(&mut s, source);
    outcome(&s, &result)
}

/// Check, rewind to the mark before the check, check again. The rewound
/// session must also be the fresh session again.
fn check_rewind_check(source: &Source, fresh: &str) {
    let mut s = session();
    let before = outcome(&s, &Ok(()));
    let mark = s.mark();
    let _ = check(&mut s, source);
    s.rewind(&mark);
    assert_same(
        source,
        "rewound to before the check",
        &before,
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
    let mut s = session();
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
    let mut s = session();
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
    let mut s = session();
    let before = outcome(&s, &Ok(()));
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
        &before,
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
/// (`goals/`, few; their tables are new).
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
    let mut sources = tier_sample(files, 8);
    sources.extend(tier_sample(projects, 4));
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
/// `cargo test --release -p stitchwort-driver --test rewind -- --ignored
/// --nocapture mark_and_rewind_cost_alone`.
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
    let mut s = session();
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
            let mut s = session();
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
    LiveProject::new(session(), name, config, sources)
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
        let mut s = session();
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
    let points: Vec<(usize, usize)> = (fresh.iter().enumerate())
        .flat_map(|(i, (_, uses))| (1..=*uses).map(move |at| (i, at)))
        .collect();
    let cancelled = par_map(STACK, &points, |&(i, at)| {
        let source = &sources[i];
        let mut s = session();
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
