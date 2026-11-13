//! The formatter's hash oracle (docs/proposals/formatter.md §4.2): a file's
//! declarations must keep their `def_hash`/`data_hash` and export flag, in
//! the same order, with the same tests, when the file is formatted. This
//! goes through the elaborator, so it is independent of the formatter's own
//! parser-level checks.
//!
//! The repository is kept formatted (on 12 Nov 2026 the formatter changed 2
//! of 819 files), so formatting the files as they are would compare nothing.
//! Instead each file is de-formatted in memory (`deformat.rs`: spacing,
//! blank lines, indentation, trailing spaces, and line breaks after commas
//! and before `|>`, all keeping the syntax tree), and the formatter is run
//! on that. Two texts come out of the de-formatter: one with only layout
//! changes, which formatting must turn back into exactly what formatting
//! the original gives, and one with line breaks too, which the formatter
//! keeps, so only its hashes are compared.
//!
//! Every file is de-formatted, formatted and compared as text (about 10 s
//! for the corpus), including the embedded std files and the files of
//! projects. Only a fixed sample of the standalone files is loaded (the
//! original and the formatted texts, in fresh sessions, as the elaborator
//! sees them), and so is a sample of the projects, with the AoC project in
//! the all tier only: loading is nearly all the cost (the all tier's
//! 2,213 s with the AoC project before this was cut down, SW-2962).
//!
//! Scope is D1019: `examples/reject`, `examples/soundness` and
//! `examples/projects/reject` are left out, and so is `crates/fmt/tests/it/golden`
//! (kept as written). The core and library under `crates/elab/src/std` are
//! compiled into the compiler and can't be loaded as a file, so they're
//! only formatted (reported).
//!
//! `FMT_HASHES=<text>` limits the run to the files and projects whose path
//! contains it, and loads all of them. `FMT_HASHES_TREE=1` checks the tree
//! printer (`stitchwort_fmt::printer`, formatter-architecture.md stage 2)
//! instead of the default formatter. `FMT_HASHES_SKIP=<n>` and
//! `FMT_HASHES_LIMIT=<n>` run a slice of the standalone files (no projects),
//! loaded in full, and the count check is off.

use std::path::{Path, PathBuf};

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId};
use stitchwort_driver::driver::{Session, all_tier, par_map, tier_sample};
use stitchwort_driver::project::{DiskFiles, Entry, Files, Target};

#[path = "../../../fmt/tests/it/support/repo_files.rs"]
mod repo_files;

use crate::deformat::deformat;

const STACK: usize = 16 * 1024 * 1024;

/// The formatter under test: the default one, or with `FMT_HASHES_TREE` set
/// the tree printer.
fn format(text: &str) -> Result<String, stitchwort_fmt::Error> {
    if std::env::var_os("FMT_HASHES_TREE").is_some() {
        stitchwort_fmt::printer::format_tree(text).map(|f| f.text)
    } else {
        stitchwort_fmt::format(text)
    }
}

const EXCLUDED: [&str; 4] = [
    "examples/reject/",
    "examples/soundness/",
    "examples/projects/reject/",
    "crates/fmt/tests/it/golden/",
];

/// Inputs left out because loading them is a resource runaway, not a
/// formatting question: each is a fuzz finding whose size is the point, and
/// together they held 4.5 GB and 1.7 GB at once (the all tier's 7.7 GB,
/// SW-2614). Their parse and formatting are still checked by the formatter's
/// own tests.
const TOO_LARGE_TO_LOAD: [&str; 2] = [
    // A `Fin` literal of 2^128 unfolds into that many `FSucc`s (SW-2467).
    "dev/fuzz-findings/2468-12893.sw",
    // `settle 2^128` builds a deep chain until the resource limit (SW-2468).
    "dev/fuzz-findings/246f-2415.sw",
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
    let g = &session.elab.ev();
    let mut decls = Vec::new();
    for i in first.0..g.env.datas().len() {
        decls.push((
            format!("data {}", g.env.datas()[i].path()),
            show(data_hash(g, DataId(i))),
        ));
    }
    for i in first.1..g.env.defs().len() {
        let d = &g.env.defs()[i];
        decls.push((
            format!("def {}", d.path()),
            format!("{} export={}", show(def_hash(g, DefId(i))), d.export()),
        ));
    }
    let tests = session.elab.tests()[first.2..]
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
    session.elab.options.limits = stitchwort_core::Limits::for_stack(STACK);
    let first = (
        session.elab.kernel.env.datas().len(),
        session.elab.kernel.env.defs().len(),
        session.elab.tests().len(),
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

/// A project whose `.sw` files read de-formatted and then formatted (with
/// the line breaks), as the formatter's output for them.
struct Reformatted(DiskFiles);

impl Files for Reformatted {
    fn include_files(&self) -> Option<std::rc::Rc<dyn stitchwort_elab::project::IncludeFiles>> {
        self.0.include_files()
    }
    fn entries(&self, dir: &str) -> std::io::Result<Vec<Entry>> {
        self.0.entries(dir)
    }
    fn read(&self, path: &str) -> std::io::Result<String> {
        let text = self.0.read(path)?;
        if path.ends_with(".sw") {
            let reformatted = deformat(path, &text).and_then(|d| format(&d.broken).ok());
            Ok(reformatted.unwrap_or(text))
        } else {
            Ok(text)
        }
    }
}

/// What checking one file found.
#[derive(Default)]
struct Checked {
    /// The formatter refuses the file as written (or the de-formatter can't
    /// read it): nothing to check.
    refused: bool,
    /// Loaded as written and formatted, with the same declarations.
    compared: bool,
    /// Loaded in neither form.
    not_loadable: bool,
    /// Formatting the layout de-formatting (with indentation) gave something
    /// other than formatting the file as written: not an error (the
    /// formatter copies some lines' indentation), only counted.
    not_restored: bool,
    failures: Vec<String>,
    applied: Vec<&'static str>,
    dropped: Vec<&'static str>,
}

/// De-formats the file at `path` and formats it, as text; with `load`, also
/// loads the original and each formatted text that differs from it, and
/// compares the declarations.
fn check_file(root: &Path, path: &str, load: bool) -> Checked {
    let text = std::fs::read_to_string(root.join(path)).unwrap();
    let mut checked = Checked::default();
    let Ok(original) = format(&text) else {
        checked.refused = true;
        return checked;
    };
    let Some(deformed) = deformat(path, &text) else {
        checked.failures.push(format!(
            "{path}: formats as written but the de-formatter can't parse it"
        ));
        return checked;
    };
    checked.applied = deformed.applied.clone();
    checked.dropped = deformed.dropped.clone();
    let mut formatted = Vec::new();
    for (what, input) in [
        ("flat", &deformed.flat),
        ("layout", &deformed.layout),
        ("breaks", &deformed.broken),
    ] {
        match format(input) {
            Ok(output) => formatted.push((what, output)),
            Err(e) => checked
                .failures
                .push(format!("{path}: de-formatted ({what}): {e}")),
        }
    }
    if let Some((_, output)) = formatted.iter().find(|(what, _)| *what == "flat")
        && *output != original
    {
        checked.failures.push(format!(
            "{path}: formatting its spacing, blank-line and trailing-space de-formatting \
             doesn't give what formatting the file gives"
        ));
    }
    if let Some((_, output)) = formatted.iter().find(|(what, _)| *what == "layout") {
        checked.not_restored = *output != original;
    }
    if !load || !checked.failures.is_empty() {
        return checked;
    }
    let loaded = |text: &str| {
        let (mut session, first) = start();
        let ok = session.load(path, text).is_ok();
        (ok, summarize(&session, first))
    };
    let (ok_before, before) = loaded(&text);
    for (what, output) in &formatted {
        if *output == text {
            continue;
        }
        let (ok_after, after) = loaded(output);
        if ok_before != ok_after {
            checked.failures.push(format!(
                "{path}: {} as written, but {} formatted from its {what} de-formatting",
                if ok_before { "loads" } else { "fails" },
                if ok_after { "loads" } else { "fails" },
            ));
        } else if ok_before {
            checked
                .failures
                .extend(compare(&format!("{path} ({what})"), &before, &after));
        }
    }
    checked.compared = ok_before && checked.failures.is_empty();
    checked.not_loadable = !ok_before;
    checked
}

fn project_failures(dir: &Path, name: &str) -> Vec<String> {
    let load = |files: &dyn Files| {
        let (mut session, first) = start();
        let result = session.load_project(files, name, &Target::Everything);
        (result.is_ok(), summarize(&session, first))
    };
    let root = dir.to_path_buf();
    let (ok_before, before) = load(&DiskFiles { root: root.clone() });
    let (ok_after, after) = load(&Reformatted(DiskFiles { root }));
    // A project that doesn't load on its own has nothing to compare.
    if !ok_before && !ok_after {
        return Vec::new();
    }
    if !ok_before || !ok_after {
        return vec![format!(
            "project {name}: loads as written: {ok_before}, de-formatted and formatted: {ok_after}"
        )];
    }
    compare(&format!("project {name}"), &before, &after)
}

/// Every `STRIDE`th standalone file is loaded in the broad tier, a quarter
/// of those in quick and lane, all of them in the all tier; likewise the projects.
const FILE_STRIDE: usize = 20;
const PROJECT_STRIDE: usize = 4;

#[test]
fn formatting_changes_no_declaration_hash() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let all: Vec<String> = repo_files::repo_files(&root, &[".sw", "stitchwort.yaml"])
        .into_iter()
        .filter(|p| !EXCLUDED.iter().any(|e| p.starts_with(e)))
        .filter(|p| !TOO_LARGE_TO_LOAD.contains(&p.as_str()))
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
    let env_count = |name: &str| {
        std::env::var(name)
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
    };
    let (skip, limit) = (env_count("FMT_HASHES_SKIP"), env_count("FMT_HASHES_LIMIT"));
    let sliced = skip.is_some() || limit.is_some();
    let projects: Vec<String> = projects.into_iter().filter(|p| p.contains(&only)).collect();

    // Every source is de-formatted and formatted; which are loaded is a
    // fixed sample, or all of a slice or of what `FMT_HASHES` names.
    let mut standalone: Vec<&str> = standalone
        .into_iter()
        .filter(|p| p.contains(&only))
        .collect();
    let (checked_files, loaded_files, projects): (Vec<&str>, Vec<&str>, Vec<String>) = if sliced {
        standalone.drain(..skip.unwrap_or(0).min(standalone.len()));
        standalone.truncate(limit.unwrap_or(usize::MAX));
        (standalone.clone(), standalone, Vec::new())
    } else {
        let checked = sources
            .iter()
            .copied()
            .filter(|p| p.contains(&only))
            .collect();
        // The AoC project, loaded twice, is checked whole in the all tier
        // only (137 s on one thread under load, 31 Oct 2026).
        let (aoc, others): (Vec<String>, Vec<String>) =
            projects.into_iter().partition(|p| p == "aoc");
        let mut projects = if only.is_empty() {
            tier_sample(others, PROJECT_STRIDE)
        } else {
            others
        };
        if !aoc.is_empty() && all_tier("formatting_changes_no_declaration_hash's AoC project") {
            projects.extend(aoc);
        }
        let loaded = if only.is_empty() {
            tier_sample(standalone, FILE_STRIDE)
        } else {
            standalone
        };
        (checked, loaded, projects)
    };

    let mut failures = Vec::new();
    let (mut compared, mut not_loadable, mut refused, mut not_restored) = (0, 0, 0, Vec::new());
    let mut applied: std::collections::BTreeMap<&str, usize> = Default::default();
    let mut dropped: std::collections::BTreeMap<&str, usize> = Default::default();
    let work: Vec<(&str, bool)> = checked_files
        .iter()
        .map(|p| (*p, loaded_files.contains(p)))
        .collect();
    for ((path, _), checked) in work.iter().zip(par_map(STACK, &work, |(p, load)| {
        check_file(&root, p, *load)
    })) {
        compared += usize::from(checked.compared);
        not_loadable += usize::from(checked.not_loadable);
        refused += usize::from(checked.refused);
        if checked.not_restored {
            not_restored.push(*path);
        }
        for name in &checked.applied {
            *applied.entry(name).or_default() += 1;
        }
        for name in &checked.dropped {
            *dropped.entry(name).or_default() += 1;
        }
        failures.extend(checked.failures);
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
    let in_dir = |dir: &str| {
        sources
            .iter()
            .filter(|p| p.starts_with(&format!("{dir}/")))
            .count()
    };
    let project_files: usize = projects.iter().map(|dir| in_dir(dir)).sum();
    println!(
        "hash oracle: {} files de-formatted and formatted ({embedded} of them embedded std \
         files, compiled into the compiler and not loadable); {compared} loaded and compared \
         ({} chosen to load; {not_loadable} didn't load on their own); {refused} refused by \
         the formatter as written; {} projects compared ({project_files} files)",
        checked_files.len(),
        loaded_files.len(),
        projects.len(),
    );
    println!("de-formatting kept the syntax tree, per transformation: {applied:?}");
    println!("de-formatting dropped, per transformation: {dropped:?}");
    println!(
        "the layout de-formatting (with indentation) formatted to something other than the \
         original's formatting in {} files, for example {:?}",
        not_restored.len(),
        &not_restored[..not_restored.len().min(5)]
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    if only.is_empty() && !sliced {
        // None went missing from the corpus, and every transformation still
        // does something.
        assert!(
            checked_files.len() > 500,
            "only {} files checked",
            checked_files.len()
        );
        assert!(compared > 5, "only {compared} files compared");
        for name in [
            "spacing",
            "blank lines",
            "declaration indent",
            "bracket indent",
            "trailing spaces",
            "break after comma",
            "break before pipe",
        ] {
            assert!(applied.contains_key(name), "{name} changed no file");
        }
    }
}
