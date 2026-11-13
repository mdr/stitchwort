//! `stitchwort sweep theorem-binders` (SW-2655): moves theorems' `∀`
//! variables, and the premises their proofs name, before the colon
//! (docs/proposals/theorem-binders.md §5; D3470, D3471), and writes only
//! what the trial check accepts.
//!
//! The rewrite is [`binder_sweep`]'s, on the syntax tree; the files are
//! then formatted. Every rewrite is checked with the "same statement"
//! promise: in a project, on the checked project (`LiveProject::trial`);
//! in the standard library, by loading an edited copy in a child process
//! and comparing every declaration's hashes with the library as it is (a
//! process reads the library only once). A theorem whose statement hash
//! moves, whose changed proof a definition mentions (a definition's hash
//! covers the proofs in it, say a structure's invariant), or that has a
//! new diagnostic, is refused: left as it was and listed, and the rest are
//! checked again, until nothing is found. With `--proofs-only` the promise
//! is "proofs only" instead: a definition whose hash moved only through the
//! proofs it embeds (its hash without proofs held) is accepted and listed.
//!
//! Exit status: 0 done (or nothing to do); 1 something couldn't be checked
//! clean; 2 refused or not understood.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Instant;

use serde_json::{Value, json};
use stitchwort_cli::project::DiskFiles;
use stitchwort_driver::binder_sweep::{self, Converted, Skipped};
use stitchwort_driver::declhash::{self, DeclHash, owner};
use stitchwort_driver::driver::Session;
use stitchwort_driver::live::{Edit, Place, Promise, TrialOutcome};
use stitchwort_syntax::ast::Decl;
use stitchwort_syntax::{DEFAULT_STACK, Diagnostic, Severity, SourceMap, parse_module_within};

use super::CacheArgs;

const CLEAN: u8 = 0;
const PROBLEMS: u8 = 1;
const REFUSED: u8 = 2;

/// Rounds of trial and refusal before giving up.
const MAX_ROUNDS: usize = 12;

pub(super) struct Args<'a> {
    pub paths: &'a [PathBuf],
    pub std: bool,
    /// The paths are single files, each checked on its own.
    pub files: bool,
    pub std_root: Option<&'a Path>,
    pub dry_run: bool,
    pub plan: bool,
    pub json: bool,
    /// Theorems to leave as they are.
    pub keep: &'a [String],
    /// Check with `Promise::ProofsOnly` instead of `SameStatement`.
    pub proofs_only: bool,
    pub project: Option<&'a Path>,
    pub cache: &'a CacheArgs,
}

/// A theorem the trial refused.
#[derive(Clone, Debug)]
struct Refusal {
    name: String,
    line: u32,
    reason: String,
}

/// One file's sweep.
#[derive(Clone, Debug, Default)]
struct FileSweep {
    /// As the project or library names it.
    path: String,
    original: String,
    /// Written names the trial refused.
    keep: BTreeSet<String>,
    refused: Vec<Refusal>,
    /// The latest sweep and formatted text.
    converted: Vec<Converted>,
    skipped: Vec<Skipped>,
    /// Why the file can't be swept at all (it doesn't lex or parse).
    error: Option<String>,
    text: String,
    seconds: f64,
}

impl FileSweep {
    fn new(path: String, original: String) -> FileSweep {
        FileSweep {
            path,
            text: original.clone(),
            original,
            ..FileSweep::default()
        }
    }

    /// Sweeps the original again, without the refused theorems, and
    /// formats the result.
    fn run(&mut self) -> Result<(), String> {
        let start = Instant::now();
        let outcome = binder_sweep::sweep(&self.original, &self.keep)
            .map_err(|e| format!("{}: {e}", self.path))?;
        self.converted = outcome.converted;
        self.skipped = outcome.skipped;
        self.text = if self.converted.is_empty() {
            self.original.clone()
        } else {
            stitchwort_fmt::format(&outcome.text).map_err(|e| format!("{}: {e}", self.path))?
        };
        self.seconds += start.elapsed().as_secs_f64();
        Ok(())
    }

    fn changed(&self) -> bool {
        self.text != self.original
    }

    /// The converted theorem `name` (a full name, or as named in its
    /// namespace) means, if any.
    fn converted_named(&self, name: &str) -> Option<&Converted> {
        self.converted.iter().find(|c| {
            name == c.name
                || name
                    .strip_suffix(c.name.as_str())
                    .is_some_and(|p| p.ends_with('.'))
        })
    }

    /// The converted theorem at `line` (from 1) of the formatted text.
    fn converted_at(&self, line: u32) -> Option<&Converted> {
        let lines = theorem_lines(&self.text);
        self.converted.iter().find(|c| {
            lines
                .get(&c.name)
                .is_some_and(|(from, to)| *from <= line && line <= *to)
        })
    }

    fn refuse(&mut self, name: &str, reason: String) {
        if let Some(c) = self.converted_named(name).cloned()
            && self.keep.insert(c.name.clone())
        {
            self.refused.push(Refusal {
                name: c.name,
                line: c.line,
                reason,
            });
        }
    }
}

/// The line (from 1) of a byte offset.
fn line_of(text: &str, offset: u32) -> u32 {
    let end = (offset as usize).min(text.len());
    text.as_bytes()[..end]
        .iter()
        .filter(|&&b| b == b'\n')
        .count() as u32
        + 1
}

/// Each theorem's first and last line (from 1), by its name as written.
fn theorem_lines(text: &str) -> BTreeMap<String, (u32, u32)> {
    let file = SourceMap::new().add("lines.sw", text);
    let Ok(module) = parse_module_within(file, text, DEFAULT_STACK) else {
        return BTreeMap::new();
    };
    let line = |offset: u32| text[..offset as usize].matches('\n').count() as u32 + 1;
    let mut out = BTreeMap::new();
    let mut current: Option<String> = None;
    for decl in &module.decls {
        match decl {
            Decl::Signature {
                name,
                theorem: true,
                span,
                ..
            } => {
                out.insert(name.text.clone(), (line(span.start), line(span.end)));
                current = Some(name.text.clone());
            }
            Decl::Equation { name, span, .. } if current.as_deref() == Some(&name.text) => {
                if let Some(range) = out.get_mut(&name.text) {
                    range.1 = line(span.end);
                }
            }
            _ => current = None,
        }
    }
    out
}

fn print_json(value: Value) {
    println!("{}", serde_json::to_string_pretty(&value).expect("JSON"));
}

fn refused(json: bool, message: String) -> ExitCode {
    if json {
        print_json(json!({ "version": 1, "status": "refused", "message": message }));
    } else {
        eprintln!("error: {message}");
    }
    ExitCode::from(REFUSED)
}

/// The `.sw` files a path names: itself, or those in a folder.
fn sw_files(path: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    if path.is_dir() {
        let mut entries: Vec<PathBuf> = std::fs::read_dir(path)?
            .map(|e| e.map(|e| e.path()))
            .collect::<Result<_, _>>()?;
        entries.sort();
        for entry in entries {
            sw_files(&entry, out)?;
        }
    } else if path.extension().is_some_and(|e| e == "sw") {
        out.push(path.to_path_buf());
    }
    Ok(())
}

fn relative(path: &Path, root: &Path) -> Option<String> {
    let full = path.canonicalize().ok()?;
    let root = root.canonicalize().ok()?;
    let rel = full.strip_prefix(&root).ok()?;
    Some(
        rel.components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/"),
    )
}

pub(super) fn theorem_binders(args: &Args) -> ExitCode {
    if args.paths.is_empty() {
        return refused(args.json, "give the files or folders to sweep".to_string());
    }
    let mut files = Vec::new();
    for p in args.paths {
        if let Err(e) = sw_files(p, &mut files) {
            return refused(args.json, format!("can't read {}: {e}", p.display()));
        }
    }
    if args.std {
        std_sweep(args, &files)
    } else if args.files {
        file_sweep(args, &files)
    } else {
        project_sweep(args, &files)
    }
}

/// Leaves the theorems `keep` names as they are, listed as refused.
fn hold_back(sweeps: &mut [FileSweep], keep: &[String]) -> Result<(), String> {
    if keep.is_empty() {
        return Ok(());
    }
    for s in sweeps.iter_mut() {
        s.run()?;
        for name in keep {
            s.refuse(name, "kept as it is (--keep)".to_string());
        }
    }
    Ok(())
}

/// The rewrites only, unchecked and unwritten.
fn plan_only(args: &Args, sweeps: &mut [FileSweep]) -> ExitCode {
    for s in sweeps.iter_mut() {
        if let Err(e) = s.run() {
            return refused(args.json, e);
        }
    }
    report(args, "plan", sweeps, false, true, &Trail::default());
    ExitCode::from(CLEAN)
}

/// One file's declarations, and the errors it didn't check with: the file
/// is loaded on its own, as `check FILE` does, and only the declarations it
/// writes are kept.
fn file_hashes(path: &str, text: &str) -> (Vec<DeclHash>, Vec<Diagnostic>) {
    let mut session = Session::for_stack(DEFAULT_STACK);
    let file = Path::new(path);
    let folder = file
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    if let Some(name) = file.file_name().and_then(|n| n.to_str()) {
        session.include_in_folder(
            std::rc::Rc::new(DiskFiles {
                root: folder.to_path_buf(),
            }),
            name,
        );
    }
    let loaded = session.load_file(path, text, None);
    let mut diagnostics = match loaded {
        Ok(_) => Vec::new(),
        Err(diagnostics) => diagnostics,
    };
    diagnostics.extend(session.warnings.iter().cloned());
    let declared = declared_names(text);
    let all = declhash::session_hashes(&session, (0, 0));
    let hashes = all
        .into_iter()
        .filter(|d| {
            declared.contains(&d.name)
                || declared.iter().any(|n| {
                    d.name.len() > n.len()
                        && d.name.starts_with(n.as_str())
                        && d.name.as_bytes()[n.len()] == b'.'
                })
        })
        .collect();
    (hashes, diagnostics)
}

/// The full names a file's declarations write, and the generated ones under
/// them (`f.eq1`, `f.%match1`).
fn declared_names(text: &str) -> BTreeSet<String> {
    let file = SourceMap::new().add("names.sw", text);
    let Ok(module) = parse_module_within(file, text, DEFAULT_STACK) else {
        return BTreeSet::new();
    };
    let prefix = module
        .namespace
        .as_ref()
        .map_or_else(|| "Main".to_string(), |n| n.path.text.clone());
    let qualify = |name: &str| format!("{prefix}.{name}");
    let mut out = BTreeSet::new();
    for decl in &module.decls {
        match decl {
            Decl::Data { name, .. }
            | Decl::Signature { name, .. }
            | Decl::Ability { name, .. }
            | Decl::Equation { name, .. } => {
                out.insert(qualify(&name.text));
            }
            Decl::Test { .. } => {}
        }
    }
    for failed in &module.failed {
        out.insert(qualify(&failed.name.text));
    }
    out
}

/// The hash of the declaration `name` (as written) in `hashes`.
fn named_hash<'a>(hashes: &'a [DeclHash], name: &str) -> Option<&'a DeclHash> {
    hashes
        .iter()
        .find(|d| d.name == name || d.name.ends_with(&format!(".{name}")))
}

fn file_sweep(args: &Args, files: &[PathBuf]) -> ExitCode {
    let mut sweeps = Vec::new();
    for f in files {
        let text = match std::fs::read_to_string(f) {
            Ok(text) => text,
            Err(e) => return refused(args.json, format!("can't read {}: {e}", f.display())),
        };
        sweeps.push(FileSweep::new(f.display().to_string(), text));
    }
    if let Err(e) = hold_back(&mut sweeps, args.keep) {
        return refused(args.json, e);
    }
    // A file that doesn't lex or parse is left as it is, and named; the
    // others are still swept.
    let sweep_all = |sweeps: &mut [FileSweep]| {
        for s in sweeps {
            if let Err(e) = s.run() {
                s.error = Some(e);
            }
        }
    };
    if args.plan {
        sweep_all(&mut sweeps);
        report(args, "plan", &sweeps, false, true, &Trail::default());
        return ExitCode::from(CLEAN);
    }
    let promise = promise(args);
    let mut before: BTreeMap<String, (Vec<DeclHash>, Vec<Diagnostic>)> = BTreeMap::new();
    let mut clean = false;
    let mut leftover = Vec::new();
    let mut proofs_changed: Vec<String> = Vec::new();
    let mut proofs_only: Vec<String> = Vec::new();
    let mut rounds: Vec<Value> = Vec::new();
    for _ in 0..MAX_ROUNDS {
        sweep_all(&mut sweeps);
        if !sweeps.iter().any(FileSweep::changed) {
            clean = true;
            break;
        }
        let mut found = 0;
        leftover.clear();
        proofs_changed.clear();
        proofs_only.clear();
        let changed: Vec<String> = sweeps
            .iter()
            .filter(|s| s.changed())
            .map(|s| s.path.clone())
            .collect();
        let mut results = Vec::new();
        for path in &changed {
            let s = sweeps
                .iter()
                .find(|s| &s.path == path)
                .expect("a swept file");
            let (after, diagnostics) = file_hashes(&s.path, &s.text);
            let (was, was_diagnostics) = before
                .entry(path.clone())
                .or_insert_with(|| file_hashes(&s.path, &s.original));
            // A theorem that didn't check before, or doesn't now, has no
            // hash on that side, and no hash compares: refuse it.
            let mut refused_here: Vec<(String, String)> = s
                .converted
                .iter()
                .filter(|c| {
                    named_hash(was, &c.name).and_then(|d| d.hash).is_none()
                        || named_hash(&after, &c.name).and_then(|d| d.hash).is_none()
                })
                .map(|c| {
                    let why = diagnostics
                        .iter()
                        .find(|d| d.severity == Severity::Error)
                        .map_or_else(
                            || "no hash for it".to_string(),
                            |d| format!("{}: {}", d.code, d.message),
                        );
                    (
                        c.name.clone(),
                        format!("it doesn't check, so can't be checked: {why}"),
                    )
                })
                .collect();
            // A diagnostic the rewrite adds is a reason to refuse the
            // theorem it lands in; one already there (the file's expected
            // error) is not.
            for d in &diagnostics {
                let already = was_diagnostics
                    .iter()
                    .any(|w| w.code == d.code && w.message == d.message);
                if already {
                    continue;
                }
                let reason = format!("{}: {}", d.code, d.message);
                let line = d.labels.first().map(|l| line_of(&s.text, l.span.start));
                match line.and_then(|line| s.converted_at(line)) {
                    Some(c) => refused_here.push((c.name.clone(), reason)),
                    None => leftover.push(format!("{}: {reason}", s.path)),
                }
            }
            let diff = declhash::compare(was, &after, &promise);
            results.push((path.clone(), refused_here, diff));
        }
        let mut all_moved = Vec::new();
        let mut any_bad = false;
        for (path, unhashed, diff) in results {
            let s = sweeps
                .iter_mut()
                .find(|s| &s.path == &path)
                .expect("a swept file");
            for (name, reason) in unhashed {
                s.refuse(&name, reason);
                found += 1;
            }
            any_bad |= !diff.is_empty();
            proofs_changed.extend(diff.proofs_changed.iter().cloned());
            proofs_only.extend(diff.proofs_only.iter().cloned());
            let moved: Vec<Moved> = diff
                .changed
                .iter()
                .map(|c| Moved {
                    name: c.name.clone(),
                    uses: c.uses.clone(),
                    reproved: c.reproved.clone(),
                })
                .collect();
            all_moved.extend(moved);
            for n in diff.added.iter().chain(&diff.removed) {
                leftover.push(format!("`{n}` added or removed"));
            }
        }
        found += refuse_moved(&mut sweeps, &all_moved, &mut leftover);
        if found == 0 && any_bad {
            found += refuse_changed_proofs(&mut sweeps, &proofs_changed, &leftover);
        }
        rounds.push(round_log(found, &leftover));
        if found == 0 {
            clean = leftover.is_empty();
            break;
        }
    }
    let trail = Trail {
        leftover,
        proofs_changed,
        proofs_only,
        rounds,
        promise: super::trial_cmd::promise_name(&promise),
    };
    finish(args, "file", &mut sweeps, clean, &trail, |s| {
        Some(PathBuf::from(&s.path))
    })
}

fn project_sweep(args: &Args, files: &[PathBuf]) -> ExitCode {
    let (project, mut live) = match super::trial_cmd::load(
        args.project,
        args.cache,
        "sweep",
        "sweep theorem-binders src",
    ) {
        Ok(loaded) => loaded,
        Err(messages) => {
            return refused(args.json, messages.join("; "));
        }
    };
    // A declaration that doesn't check has no hash, and no hash compares
    // equal to none: the trial would see nothing.
    let unchecked: Vec<String> = live
        .declaration_hashes()
        .into_iter()
        .filter(|d| d.hash.is_none())
        .map(|d| d.name)
        .collect();
    if !unchecked.is_empty() && !args.plan {
        return refused(
            args.json,
            format!(
                "the project doesn't check (no hash for {}): fix it first",
                unchecked.join(", ")
            ),
        );
    }
    let mut sweeps = Vec::new();
    for f in files {
        let Some(path) = relative(f, &project.dir) else {
            return refused(args.json, format!("{} is not in the project", f.display()));
        };
        let Some(text) = live.text(&path) else {
            return refused(
                args.json,
                format!("{path} is not one of the project's files"),
            );
        };
        sweeps.push(FileSweep::new(path, text.to_string()));
    }
    if let Err(e) = hold_back(&mut sweeps, args.keep) {
        return refused(args.json, e);
    }
    if args.plan {
        return plan_only(args, &mut sweeps);
    }
    let promise = promise(args);
    let mut clean = false;
    let mut leftover = Vec::new();
    let mut proofs_changed: Vec<String> = Vec::new();
    let mut proofs_only: Vec<String> = Vec::new();
    let mut rounds: Vec<Value> = Vec::new();
    for _ in 0..MAX_ROUNDS {
        for s in sweeps.iter_mut() {
            if let Err(e) = s.run() {
                return refused(args.json, e);
            }
        }
        let edits: Vec<Edit> = sweeps
            .iter()
            .filter(|s| s.changed())
            .map(|s| whole_file(&s.path, &s.original, &s.text))
            .collect();
        if edits.is_empty() {
            clean = true;
            break;
        }
        let trial = match live.trial(&edits, &promise) {
            Ok(TrialOutcome::Checked(trial)) => trial,
            Ok(TrialOutcome::Refused(refusals)) => {
                let messages: Vec<String> =
                    refusals.iter().map(|r| r.describe("the sweep")).collect();
                return refused(args.json, messages.join("; "));
            }
            Err(_) => return refused(args.json, "the check was cancelled".to_string()),
        };
        let problems = trial.problems.clone();
        proofs_changed = trial.proofs_changed.clone();
        proofs_only = trial.proofs_only.clone();
        let _ = live.restore(trial);
        if problems.is_empty() {
            clean = true;
            break;
        }
        let mut found = 0;
        leftover.clear();
        for d in &problems.diagnostics {
            let reason = format!("{}: {}", d.code, d.message);
            let Some(s) = sweeps.iter_mut().find(|s| s.path == d.path) else {
                leftover.push(format!("{}: {reason}", d.path));
                continue;
            };
            let name = d
                .declaration
                .as_deref()
                .and_then(|n| s.converted_named(n))
                .or_else(|| s.converted_at(d.range[0] + 1))
                .map(|c| c.name.clone());
            match name {
                Some(name) => {
                    s.refuse(&name, reason);
                    found += 1;
                }
                None => leftover.push(format!("{}: {reason}", d.path)),
            }
        }
        let moved: Vec<Moved> = problems
            .changed
            .iter()
            .map(|c| Moved {
                name: c.name.clone(),
                uses: c.uses.clone(),
                reproved: c.reproved.clone(),
            })
            .collect();
        found += refuse_moved(&mut sweeps, &moved, &mut leftover);
        if found == 0 {
            // A change no converted theorem accounts for directly: the
            // theorems whose proofs changed are the suspects.
            found += refuse_changed_proofs(&mut sweeps, &proofs_changed, &leftover);
        }
        rounds.push(round_log(found, &leftover));
        if found == 0 {
            break;
        }
    }
    let trail = Trail {
        leftover,
        proofs_changed,
        proofs_only,
        rounds,
        promise: super::trial_cmd::promise_name(&promise),
    };
    finish(args, "project", &mut sweeps, clean, &trail, |s| {
        Some(project.dir.join(&s.path))
    })
}

fn promise(args: &Args) -> Promise {
    let renames = BTreeMap::new();
    if args.proofs_only {
        Promise::ProofsOnly { renames }
    } else {
        Promise::SameStatement { renames }
    }
}

/// A declaration whose hash moved against the promise.
struct Moved {
    name: String,
    /// Another moved declaration it mentions.
    uses: Option<String>,
    /// The re-proved theorems it mentions, directly or through others
    /// (full names).
    reproved: Vec<String>,
}

/// Refuses the converted theorems that `moved` leads back to, and returns
/// how many; what none accounts for goes in `leftover`. Only a moved
/// declaration that mentions nothing else that moved, itself or through
/// the re-proved theorems it mentions, is a root; the rest may have moved
/// only because of a root. For each root, in order of
/// precision: the converted theorems whose re-proved proofs it mentions,
/// directly or through other re-proved theorems (a definition's hash
/// covers the proofs it mentions, say a structure's invariant); or itself,
/// a converted theorem whose statement moved. A converted theorem whose
/// statement moved along with something it mentions waits for the next
/// round, unless nothing else is found.
fn refuse_moved(sweeps: &mut [FileSweep], moved: &[Moved], leftover: &mut Vec<String>) -> usize {
    let mut found = 0;
    let refuse = |sweeps: &mut [FileSweep], name: &str, reason: String| -> bool {
        match sweeps
            .iter_mut()
            .find(|s| s.converted_named(name).is_some())
        {
            Some(s) => {
                s.refuse(name, reason);
                true
            }
            None => false,
        }
    };
    let mut waiting = Vec::new();
    for m in moved {
        let converted = sweeps.iter().any(|s| s.converted_named(&m.name).is_some());
        let mut hit = false;
        match &m.uses {
            None => {
                for r in &m.reproved {
                    hit |= refuse(
                        sweeps,
                        owner(r),
                        format!(
                            "its proof changed, and `{}` mentions it, so its hash would move",
                            m.name
                        ),
                    );
                }
                if converted {
                    hit |= refuse(sweeps, &m.name, "its statement's hash moved".to_string());
                }
            }
            // What it mentions is among `moved`, and is dealt with there.
            Some(_) if converted => {
                waiting.push(m);
                continue;
            }
            Some(_) => {}
        }
        if hit {
            found += 1;
        } else {
            let mut line = format!("`{}` changed", m.name);
            if let Some(u) = &m.uses {
                line += &format!(" (it mentions `{u}`, which changed)");
            } else if !m.reproved.is_empty() {
                line += &format!(
                    " (it mentions the re-proved {})",
                    m.reproved
                        .iter()
                        .map(|r| format!("`{r}`"))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            leftover.push(line);
        }
    }
    if found == 0 {
        for m in waiting {
            let reason = format!(
                "its statement's hash moved (it mentions `{}`, which moved too)",
                m.uses.as_deref().unwrap_or_default()
            );
            if refuse(sweeps, &m.name, reason) {
                found += 1;
            }
        }
    }
    found
}

/// A round of the trial, for the JSON report: how many refusals it found,
/// and the changes that mention nothing else changed (where to look).
fn round_log(found: usize, leftover: &[String]) -> Value {
    json!({
        "found": found,
        "roots": leftover
            .iter()
            .filter(|l| !l.contains("which changed)"))
            .collect::<Vec<_>>(),
    })
}

fn refuse_changed_proofs(
    sweeps: &mut [FileSweep],
    proofs_changed: &[String],
    leftover: &[String],
) -> usize {
    let mut found = 0;
    let because = format!(
        "its proof changed, and something it may be used by changed: {}",
        leftover.join("; ")
    );
    for name in proofs_changed {
        for s in sweeps.iter_mut() {
            if s.converted_named(name).is_some() {
                s.refuse(name, because.clone());
                found += 1;
            }
        }
    }
    found
}

fn whole_file(path: &str, old: &str, new: &str) -> Edit {
    let lines = old.split('\n').count() as u32 - 1;
    let last = old.rsplit('\n').next().unwrap_or("");
    Edit {
        place: Place::Program(path.to_string()),
        range: [0, 0, lines, last.encode_utf16().count() as u32],
        new_text: new.to_string(),
    }
}

/// The library's hashes, read by a child process from `dir`.
fn library_hashes(dir: &Path) -> Result<Vec<DeclHash>, String> {
    let exe = std::env::current_exe().map_err(|e| format!("can't find myself: {e}"))?;
    let output = Command::new(exe)
        .arg("--std-dir")
        .arg(dir)
        .args(["hash", "--std", "--json", "--uses"])
        .output()
        .map_err(|e| format!("can't run the hash: {e}"))?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).trim().to_string());
    }
    serde_json::from_slice::<Value>(&output.stdout)
        .ok()
        .and_then(|v| {
            v.get("declarations")?
                .as_array()?
                .iter()
                .map(super::trial_cmd::decl_from_json)
                .collect()
        })
        .ok_or_else(|| "can't read the library's hashes".to_string())
}

fn copy_dir(from: &Path, to: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(to)?;
    for entry in std::fs::read_dir(from)? {
        let entry = entry?;
        let target = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_dir(&entry.path(), &target)?;
        } else {
            std::fs::copy(entry.path(), &target)?;
        }
    }
    Ok(())
}

fn default_std_root() -> Option<PathBuf> {
    let mut dir = std::env::current_dir().ok()?;
    loop {
        let candidate = dir.join("crates/elab/src/std");
        if candidate.is_dir() {
            return Some(candidate);
        }
        if !dir.pop() {
            return None;
        }
    }
}

fn std_sweep(args: &Args, files: &[PathBuf]) -> ExitCode {
    let Some(root) = args
        .std_root
        .map(Path::to_path_buf)
        .or_else(default_std_root)
    else {
        return refused(
            args.json,
            "can't find the library's source: give --std-root".to_string(),
        );
    };
    let mut sweeps = Vec::new();
    for f in files {
        let Some(path) = relative(f, &root) else {
            return refused(
                args.json,
                format!("{} is not in {}", f.display(), root.display()),
            );
        };
        let text = match std::fs::read_to_string(f) {
            Ok(text) => text,
            Err(e) => return refused(args.json, format!("can't read {}: {e}", f.display())),
        };
        sweeps.push(FileSweep::new(path, text));
    }
    if let Err(e) = hold_back(&mut sweeps, args.keep) {
        return refused(args.json, e);
    }
    if args.plan {
        return plan_only(args, &mut sweeps);
    }
    let before = match library_hashes(&root) {
        Ok(before) => before,
        Err(e) => return refused(args.json, format!("the library doesn't load as it is: {e}")),
    };
    let copy = std::env::temp_dir().join(format!("stitchwort-sweep-std-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&copy);
    if let Err(e) = copy_dir(&root, &copy) {
        return refused(args.json, format!("can't copy the library: {e}"));
    }
    let promise = promise(args);
    let mut clean = false;
    let mut leftover = Vec::new();
    let mut proofs_changed: Vec<String> = Vec::new();
    let mut proofs_only: Vec<String> = Vec::new();
    let mut rounds: Vec<Value> = Vec::new();
    for _ in 0..MAX_ROUNDS {
        for s in sweeps.iter_mut() {
            if let Err(e) = s.run() {
                let _ = std::fs::remove_dir_all(&copy);
                return refused(args.json, e);
            }
            if let Err(e) = std::fs::write(copy.join(&s.path), &s.text) {
                let _ = std::fs::remove_dir_all(&copy);
                return refused(args.json, format!("can't write the copy: {e}"));
            }
        }
        if !sweeps.iter().any(FileSweep::changed) {
            clean = true;
            break;
        }
        let mut found = 0;
        leftover.clear();
        match library_hashes(&copy) {
            Err(report) => {
                // The edited library doesn't load: the report names a file
                // and line.
                for s in sweeps.iter_mut() {
                    for (line, error) in lines_named(&report, &s.path) {
                        if let Some(name) = s.converted_at(line).map(|c| c.name.clone()) {
                            s.refuse(&name, format!("doesn't check: {error}"));
                            found += 1;
                        }
                    }
                }
                if found == 0 {
                    leftover.push(report);
                }
            }
            Ok(after) => {
                let diff = declhash::compare(&before, &after, &promise);
                proofs_changed = diff.proofs_changed.clone();
                proofs_only = diff.proofs_only.clone();
                if diff.is_empty() {
                    clean = true;
                    break;
                }
                let moved: Vec<Moved> = diff
                    .changed
                    .iter()
                    .map(|c| Moved {
                        name: c.name.clone(),
                        uses: c.uses.clone(),
                        reproved: c.reproved.clone(),
                    })
                    .collect();
                found += refuse_moved(&mut sweeps, &moved, &mut leftover);
                for n in diff.added.iter().chain(&diff.removed) {
                    leftover.push(format!("`{n}` added or removed"));
                }
                if found == 0 {
                    found += refuse_changed_proofs(&mut sweeps, &diff.proofs_changed, &leftover);
                }
            }
        }
        rounds.push(round_log(found, &leftover));
        if found == 0 {
            break;
        }
    }
    let _ = std::fs::remove_dir_all(&copy);
    let trail = Trail {
        leftover,
        proofs_changed,
        proofs_only,
        rounds,
        promise: super::trial_cmd::promise_name(&promise),
    };
    finish(args, "std", &mut sweeps, clean, &trail, |s| {
        Some(root.join(&s.path))
    })
}

/// The line numbers a report gives after `path:`, each with the error
/// it's under.
fn lines_named<'a>(report: &'a str, path: &str) -> Vec<(u32, &'a str)> {
    let mut out = Vec::new();
    let needle = format!("{path}:");
    let mut error = "";
    for line in report.lines() {
        if let Some(at) = line.find("Error: ") {
            error = line[at + "Error: ".len()..].trim();
        }
        if let Some(at) = line.find(&needle) {
            let digits: String = line[at + needle.len()..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            if let Ok(n) = digits.parse() {
                out.push((n, error));
            }
        }
    }
    out
}

/// What the rounds of trials left: what no refusal accounted for in the
/// last, the proofs that changed with their statements kept, and each
/// round's log.
#[derive(Default)]
struct Trail {
    leftover: Vec<String>,
    proofs_changed: Vec<String>,
    /// Under the "proofs only" promise: the definitions and data types
    /// whose proofs changed, accepted.
    proofs_only: Vec<String>,
    rounds: Vec<Value>,
    promise: &'static str,
}

fn finish(
    args: &Args,
    mode: &str,
    sweeps: &mut [FileSweep],
    clean: bool,
    trail: &Trail,
    disk: impl Fn(&FileSweep) -> Option<PathBuf>,
) -> ExitCode {
    let write = clean && !args.dry_run;
    if write {
        for s in sweeps.iter().filter(|s| s.changed()) {
            let Some(path) = disk(s) else { continue };
            if let Err(e) = std::fs::write(&path, &s.text) {
                return refused(args.json, format!("can't write {}: {e}", path.display()));
            }
        }
    }
    if !clean && !args.json {
        for l in &trail.leftover {
            eprintln!("unaccounted for: {l}");
        }
    }
    report(args, mode, sweeps, write, clean, trail);
    ExitCode::from(if clean { CLEAN } else { PROBLEMS })
}

fn report(
    args: &Args,
    mode: &str,
    sweeps: &[FileSweep],
    written: bool,
    clean: bool,
    trail: &Trail,
) {
    let proofs_changed = &trail.proofs_changed;
    let mut by_reason: BTreeMap<&str, usize> = BTreeMap::new();
    for s in sweeps {
        for k in &s.skipped {
            *by_reason.entry(k.reason.code()).or_default() += 1;
        }
    }
    let converted: usize = sweeps.iter().map(|s| s.converted.len()).sum();
    let skipped: usize = sweeps.iter().map(|s| s.skipped.len()).sum();
    let refused: usize = sweeps.iter().map(|s| s.refused.len()).sum();
    if args.json {
        let files: Vec<Value> = sweeps
            .iter()
            .map(|s| {
                json!({
                    "file": s.path,
                    "seconds": s.seconds,
                    "error": s.error,
                    "converted": s.converted.iter().map(|c| json!({
                        "name": c.name,
                        "line": c.line,
                        "eta": c.eta,
                        "before": c.before,
                        "after": c.after,
                    })).collect::<Vec<_>>(),
                    "skipped": s.skipped.iter().map(|k| json!({
                        "name": k.name,
                        "line": k.line,
                        "reason": k.reason.code(),
                        "message": k.reason.describe(),
                    })).collect::<Vec<_>>(),
                    "refused": s.refused.iter().map(|r| json!({
                        "name": r.name,
                        "line": r.line,
                        "reason": r.reason,
                    })).collect::<Vec<_>>(),
                })
            })
            .collect();
        print_json(json!({
            "version": 1,
            "mode": mode,
            "promise": trail.promise,
            "status": if clean { "clean" } else { "problems" },
            "written": written,
            "converted": converted,
            "skipped": skipped,
            "refused": refused,
            "skippedByReason": by_reason,
            "proofsChanged": proofs_changed,
            "proofsOnly": trail.proofs_only,
            "rounds": trail.rounds,
            "files": files,
        }));
        return;
    }
    for s in sweeps {
        println!(
            "{}: {} converted, {} skipped, {} refused ({:.2} s)",
            s.path,
            s.converted.len(),
            s.skipped.len(),
            s.refused.len(),
            s.seconds
        );
        if let Some(error) = &s.error {
            println!("  can't sweep it: {error}");
        }
        for k in &s.skipped {
            println!(
                "  skipped {} (line {}): {}",
                k.name,
                k.line,
                k.reason.describe()
            );
        }
        for r in &s.refused {
            println!("  refused {} (line {}): {}", r.name, r.line, r.reason);
        }
    }
    println!("{converted} converted, {skipped} skipped, {refused} refused");
    if !proofs_changed.is_empty() {
        println!(
            "{} proof(s) changed with the statement kept",
            proofs_changed.len()
        );
    }
    for name in &trail.proofs_only {
        println!("only proofs changed in {name}");
    }
    for (reason, n) in &by_reason {
        println!("  skipped {reason}: {n}");
    }
    if written {
        println!("written");
    } else if clean {
        println!("nothing was written");
    } else {
        println!("not clean: nothing was written");
    }
}
