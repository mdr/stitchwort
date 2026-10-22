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

use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;

use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{Session, par_map, slow_tier, slow_tier_on};
use stitchwort_driver::nav::index_json;
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::render::render;
use stitchwort_driver::rewind::Cancelled;
use stitchwort_elab::cache::canonical_dump;
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
    s.elab.recheck_namespaces = true;
    let result = check(&mut s, source);
    assert_same(
        source,
        "each namespace rewound",
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
/// slow tier, every eighth file and every fourth project (a fixed sample).
fn examples() -> Vec<Source> {
    let mut files = Vec::new();
    for dir in ["accept", "extract", "reject", "soundness"] {
        files.extend(example_files(dir));
    }
    let mut projects = example_projects("accept");
    projects.extend(example_projects("reject"));
    assert!(!files.is_empty() && !projects.is_empty());
    if slow_tier_on() {
        files.extend(projects);
        return files;
    }
    let mut sources: Vec<Source> = files.into_iter().step_by(8).collect();
    sources.extend(projects.into_iter().step_by(4));
    sources
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
    if !slow_tier("rewinding_changes_nothing_for_the_aoc_project") {
        return;
    }
    stitchwort_driver::driver::with_stack(STACK, || {
        let source = aoc();
        assert_rewinding_changes_nothing(&source);
        // What a mark and a rewind cost after the whole project is checked
        // (`--nocapture` shows it).
        let mut s = session();
        let empty = s.mark();
        let _ = check(&mut s, &source);
        let t = std::time::Instant::now();
        let mark = s.mark();
        let marked = t.elapsed();
        let t = std::time::Instant::now();
        s.rewind(&mark);
        let rewound = t.elapsed();
        let t = std::time::Instant::now();
        s.rewind(&empty);
        eprintln!(
            "aoc with navigation: mark {:.2} ms, rewind to it {:.2} ms, rewind to the start {:.2} ms",
            marked.as_secs_f64() * 1000.0,
            rewound.as_secs_f64() * 1000.0,
            t.elapsed().as_secs_f64() * 1000.0
        );
    });
}

/// Cancelled from another thread at various moments of a check of `aoc`:
/// either it finished first, or it says it was cancelled; either way the
/// next check in the same session gives what a fresh one does. How
/// promptly it stopped is printed (`--nocapture`).
#[test]
fn a_check_cancelled_part_way_rewinds() {
    if !slow_tier("a_check_cancelled_part_way_rewinds") {
        return;
    }
    stitchwort_driver::driver::with_stack(STACK, || {
        let source = aoc();
        let fresh = fresh(&source);
        let mut cancelled = 0;
        for delay_ms in [1, 10, 50, 150, 400, 900] {
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
                    cancelled += 1;
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
        assert!(cancelled > 0, "no check was cancelled");
    });
}
