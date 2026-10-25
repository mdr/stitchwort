//! The formatter's hash oracle (docs/proposals/formatter.md §4.2): every
//! tracked `.sw` file that loads, and every accepted project, is loaded as
//! written and as formatted, in fresh sessions, and every declaration must
//! have the same `def_hash`/`data_hash` and export flag, in the same order,
//! with the same tests. This goes through the elaborator, so it is
//! independent of the formatter's own parser-level checks.
//!
//! Scope is D1019: `examples/reject`, `examples/soundness` and
//! `examples/projects/reject` are left out, and so is `crates/fmt/tests/golden`
//! (kept as written). The core and library under `crates/elab/src/std` are
//! compiled into the compiler and can't be loaded as a file, so they're
//! skipped (reported).
//!
//! `FMT_HASHES=<text>` limits the run to the files and projects whose path
//! contains it.

use std::path::{Path, PathBuf};

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{Session, par_map};
use stitchwort_driver::project::{DiskFiles, Entry, Files, Target};

#[path = "../../fmt/tests/support/repo_files.rs"]
mod repo_files;

const STACK: usize = 16 * 1024 * 1024;

const EXCLUDED: [&str; 4] = [
    "examples/reject/",
    "examples/soundness/",
    "examples/projects/reject/",
    "crates/fmt/tests/golden/",
];

/// Compiled into the compiler: not loadable as files.
const EMBEDDED: &str = "crates/elab/src/std/";

fn show(h: stitchwort_core::budget::Result<Option<ContentHash>>) -> String {
    match h {
        Ok(Some(h)) => h.hex(),
        _ => "<none>".to_string(),
    }
}

/// What the declarations a session added are: the hash (and for a
/// definition whether it is exported), in declaration order, then the tests.
struct Summary {
    decls: Vec<(String, String)>,
    tests: Vec<String>,
}

fn summarize(session: &Session, first: (usize, usize, usize)) -> Summary {
    let g = &session.elab.globals;
    let mut decls = Vec::new();
    for i in first.0..g.datas.len() {
        decls.push((
            format!("data {}", g.datas[i].path),
            show(data_hash(g, DataId(i))),
        ));
    }
    for i in first.1..g.defs.len() {
        let d = &g.defs[i];
        decls.push((
            format!("def {}", d.path),
            format!("{} export={}", show(def_hash(g, DefId(i))), d.export),
        ));
    }
    let tests = session.elab.tests[first.2..]
        .iter()
        .map(|t| {
            format!(
                "test {} (namespace `{}`, library {})",
                t.name, t.namespace, t.library
            )
        })
        .collect();
    Summary { decls, tests }
}

fn start() -> (Session, (usize, usize, usize)) {
    // Lazy: the library files a declaration uses load on demand.
    let mut session = Session::new();
    session.elab.limits = stitchwort_core::Limits::for_stack(STACK);
    let first = (
        session.elab.globals.datas.len(),
        session.elab.globals.defs.len(),
        session.elab.tests.len(),
    );
    (session, first)
}

fn compare(what: &str, before: &Summary, after: &Summary) -> Vec<String> {
    let mut out = Vec::new();
    for (key, was) in &before.decls {
        match after.decls.iter().find(|(k, _)| k == key) {
            None => out.push(format!(
                "{what}: {key} is missing after formatting (was {was})"
            )),
            Some((_, now)) if now != was => out.push(format!(
                "{what}: {key}\n    original:  {was}\n    formatted: {now}"
            )),
            _ => {}
        }
    }
    for (key, now) in &after.decls {
        if !before.decls.iter().any(|(k, _)| k == key) {
            out.push(format!("{what}: {key} appears after formatting ({now})"));
        }
    }
    let order = |s: &Summary| s.decls.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>();
    if out.is_empty() && order(before) != order(after) {
        out.push(format!("{what}: declarations are in a different order"));
    }
    if before.tests != after.tests {
        out.push(format!(
            "{what}: the tests differ\n    original:  {:?}\n    formatted: {:?}",
            before.tests, after.tests
        ));
    }
    out
}

/// A project whose `.sw` files read as formatted (when they format).
struct Formatted(DiskFiles);

impl Files for Formatted {
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        self.0.include_files()
    }
    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>> {
        self.0.entries(dir)
    }
    fn read(&self, path: &str) -> std::io::Result<String> {
        let text = self.0.read(path)?;
        if path.ends_with(".sw") {
            Ok(stitchwort_fmt::format(&text).unwrap_or(text))
        } else {
            Ok(text)
        }
    }
}

enum Outcome {
    Compared,
    /// Doesn't load on its own (as written and formatted alike).
    NotLoadable,
    /// The formatter refuses it.
    Refused,
    Failures(Vec<String>),
}

fn file_outcome(root: &Path, path: &str) -> Outcome {
    let text = std::fs::read_to_string(root.join(path)).unwrap();
    let Ok(formatted) = stitchwort_fmt::format(&text) else {
        return Outcome::Refused;
    };
    let load = |text: &str| {
        let (mut session, first) = start();
        let loaded = session.load(path, text).is_ok();
        (loaded, summarize(&session, first))
    };
    let (ok_before, before) = load(&text);
    let (ok_after, after) = load(&formatted);
    if ok_before != ok_after {
        return Outcome::Failures(vec![format!(
            "{path}: {} as written, but {} formatted",
            if ok_before { "loads" } else { "fails" },
            if ok_after { "loads" } else { "fails" },
        )]);
    }
    if !ok_before {
        return Outcome::NotLoadable;
    }
    let failures = compare(path, &before, &after);
    if failures.is_empty() {
        Outcome::Compared
    } else {
        Outcome::Failures(failures)
    }
}

fn project_failures(dir: &Path, name: &str) -> Vec<String> {
    let load = |files: &dyn Files| {
        let (mut session, first) = start();
        let result = session.load_project(files, name, &Target::Everything);
        (result.is_ok(), summarize(&session, first))
    };
    let root = dir.to_path_buf();
    let (ok_before, before) = load(&DiskFiles { root: root.clone() });
    let (ok_after, after) = load(&Formatted(DiskFiles { root }));
    if !ok_before || !ok_after {
        return vec![format!(
            "project {name}: loads as written: {ok_before}, formatted: {ok_after}"
        )];
    }
    compare(&format!("project {name}"), &before, &after)
}

#[test]
fn formatting_changes_no_declaration_hash() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let all: Vec<String> = repo_files::repo_files(&root, &[".sw", "stitchwort.yaml"])
        .into_iter()
        .filter(|p| !EXCLUDED.iter().any(|e| p.starts_with(e)))
        .collect();

    // Project roots: the folders of the tracked `stitchwort.yaml`s.
    let mut projects: Vec<String> = all
        .iter()
        .filter_map(|p| p.strip_suffix("stitchwort.yaml"))
        .map(|p| p.trim_end_matches('/').to_string())
        .collect();
    projects.sort();
    projects.dedup();
    let in_project = |p: &str| {
        projects
            .iter()
            .any(|dir| !dir.is_empty() && p.starts_with(&format!("{dir}/")))
    };
    let sources: Vec<&str> = all
        .iter()
        .map(String::as_str)
        .filter(|p| p.ends_with(".sw"))
        .collect();
    let embedded = sources.iter().filter(|p| p.starts_with(EMBEDDED)).count();
    let standalone: Vec<&str> = sources
        .iter()
        .copied()
        .filter(|p| !p.starts_with(EMBEDDED) && !in_project(p))
        .collect();
    assert!(
        standalone.len() > 100,
        "found only {} files",
        standalone.len()
    );
    assert!(
        projects.len() >= 10,
        "found only {} projects",
        projects.len()
    );

    let only = std::env::var("FMT_HASHES").unwrap_or_default();
    let standalone: Vec<&str> = standalone
        .into_iter()
        .filter(|p| p.contains(&only))
        .collect();
    let projects: Vec<String> = projects.into_iter().filter(|p| p.contains(&only)).collect();

    let mut failures = Vec::new();
    let (mut compared, mut not_loadable, mut refused) = (0, 0, 0);
    for outcome in par_map(STACK, &standalone, |p| file_outcome(&root, p)) {
        match outcome {
            Outcome::Compared => compared += 1,
            Outcome::NotLoadable => not_loadable += 1,
            Outcome::Refused => refused += 1,
            Outcome::Failures(f) => failures.extend(f),
        }
    }
    for f in par_map(STACK, &projects, |dir| {
        let name = Path::new(dir.as_str())
            .file_name()
            .unwrap()
            .to_string_lossy()
            .to_string();
        project_failures(&root.join(dir), &name)
    }) {
        failures.extend(f);
    }
    let project_files: usize = projects
        .iter()
        .map(|dir| {
            sources
                .iter()
                .filter(|p| p.starts_with(&format!("{dir}/")))
                .count()
        })
        .sum();
    println!(
        "hash oracle: {compared} files compared; skipped {not_loadable} that don't load on \
         their own and {refused} the formatter refuses, and {embedded} embedded std files \
         (compiled into the compiler); {} projects compared ({project_files} files)",
        projects.len(),
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    if only.is_empty() {
        assert!(compared > 100, "only {compared} files compared");
    }
}
