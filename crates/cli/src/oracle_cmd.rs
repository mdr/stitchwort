//! `stitchwort oracle readings|builds` (SW-3111): the deletion oracle of
//! docs/reviews/SW-3105-silent-read.md §4.6 and
//! docs/proposals/bool-as-proposition-building.md §5.1.
//!
//! Each site is tried alone, on the file's original text:
//!
//! - `readings`: delete one `.read`;
//! - `builds`: replace one call of a build helper (`Bool.falseOfNotTrue x p`,
//!   `(List.memContains xs x).backward p`, and the others in
//!   [`oracle_sites`]) by its proof argument.
//!
//! The edited file is checked, and the site is one of
//!
//! - **needed**: it doesn't check (the `.read` or helper still does a job);
//! - **redundant** (`readings`) or **removable** (`builds`): it checks, and
//!   the meaning is kept: every statement has the same hash and every
//!   definition the same hash without the proofs inside it
//!   (`Promise::ProofsOnly`; the declarations whose proofs changed are
//!   listed, not counted against it). `removable` is the sweep's work list;
//! - **changed**: it checks, and a statement or a definition's meaning moved.
//!   This is the bad outcome, a silent change of meaning;
//! - **unparseable**: the edit left text that doesn't parse (the token
//!   heuristic of [`oracle_sites`] misjudged where a call ends); not counted
//!   against anything.
//!
//! The checking is the sweep's: in a project on the checked project (one
//! `LiveProject::trial` per site, incremental); with `--files` each file on
//! its own; with `--std` an edited copy of the library in a child process
//! (a full library load per site, so slow: the file's declarations are
//! compared with the library as it is).
//!
//! Exit status: 0 nothing changed meaning; 1 a site changed meaning; 2
//! refused or not understood.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use serde_json::{Value, json};
use stitchwort_driver::declhash::{self, DeclHash};
use stitchwort_driver::live::{LiveProject, Place, Promise, TrialOutcome};
use stitchwort_syntax::{DEFAULT_STACK, Severity, SourceMap, parse_module_within};

use super::CacheArgs;
use super::oracle_sites::{self, Half, Site};
use super::sweep_cmd::{
    copy_dir, default_std_root, file_hashes, library_hashes, relative, sw_files, whole_file,
};

const CLEAN: u8 = 0;
const PROBLEMS: u8 = 1;
const REFUSED: u8 = 2;

pub(super) struct Args<'a> {
    pub half: Half,
    pub paths: &'a [PathBuf],
    pub std: bool,
    /// The paths are single files, each checked on its own.
    pub files: bool,
    pub std_root: Option<&'a Path>,
    /// Try at most this many sites, in file and line order.
    pub limit: Option<usize>,
    pub json: bool,
    pub project: Option<&'a Path>,
    pub cache: &'a CacheArgs,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Verdict {
    /// Doesn't check: why, as the first error says.
    Needed(String),
    /// Checks with the meaning kept; the declarations whose proofs (or the
    /// proofs inside them) changed.
    Same(Vec<String>),
    /// Checks, and these declarations changed meaning.
    Changed(Vec<String>),
    Unparseable,
}

impl Verdict {
    fn word(&self, half: Half) -> &'static str {
        match (self, half) {
            (Verdict::Needed(_), _) => "needed",
            (Verdict::Same(_), Half::Readings) => "redundant",
            (Verdict::Same(_), Half::Builds) => "removable",
            (Verdict::Changed(_), _) => "changed",
            (Verdict::Unparseable, _) => "unparseable",
        }
    }
}

/// Checks an edited file against the original and says what became of it.
trait Judge {
    /// Whether the file as it is can be judged: a file that already fails
    /// would make every site look redundant. The reason if not.
    fn ready(&mut self, _path: &str, _original: &str) -> Result<(), String> {
        Ok(())
    }
    fn judge(&mut self, path: &str, original: &str, edited: &str) -> Verdict;
}

fn promise() -> Promise {
    Promise::ProofsOnly {
        renames: BTreeMap::new(),
    }
}

fn first_line(message: &str) -> String {
    message.lines().next().unwrap_or("").trim().to_string()
}

/// A project, checked incrementally.
struct ProjectJudge {
    live: LiveProject,
}

impl Judge for ProjectJudge {
    fn judge(&mut self, path: &str, original: &str, edited: &str) -> Verdict {
        let edit = whole_file(path, original, edited);
        let trial = match self.live.trial(&[edit], &promise()) {
            Ok(TrialOutcome::Checked(trial)) => trial,
            Ok(TrialOutcome::Refused(refusals)) => {
                return Verdict::Needed(
                    refusals
                        .first()
                        .map_or_else(String::new, |r| r.describe("the edit")),
                );
            }
            Err(_) => return Verdict::Needed("the check was cancelled".to_string()),
        };
        let problems = trial.problems.clone();
        let reproved: Vec<String> = trial
            .proofs_only
            .iter()
            .chain(&trial.proofs_changed)
            .cloned()
            .collect();
        let _ = self.live.restore(trial);
        if let Some(error) = problems
            .diagnostics
            .iter()
            .find(|d| d.severity == Severity::Error)
        {
            return Verdict::Needed(format!(
                "{} (line {}): {}",
                error.code,
                error.range[0] + 1,
                first_line(&error.message)
            ));
        }
        if problems.changed.is_empty() {
            Verdict::Same(reproved)
        } else {
            Verdict::Changed(
                problems
                    .changed
                    .iter()
                    .map(|c| format!("{}.{}", c.namespace, c.name))
                    .collect(),
            )
        }
    }
}

/// Each file on its own, as `check FILE` loads it.
#[derive(Default)]
struct FileJudge {
    before: BTreeMap<String, (Vec<DeclHash>, Vec<stitchwort_syntax::Diagnostic>)>,
}

impl Judge for FileJudge {
    fn ready(&mut self, path: &str, original: &str) -> Result<(), String> {
        let (_, diagnostics) = self
            .before
            .entry(path.to_string())
            .or_insert_with(|| file_hashes(path, original));
        match diagnostics.iter().find(|d| d.severity == Severity::Error) {
            Some(d) => Err(format!(
                "it doesn't check on its own: {}: {}",
                d.code,
                first_line(&d.message)
            )),
            None => Ok(()),
        }
    }

    fn judge(&mut self, path: &str, original: &str, edited: &str) -> Verdict {
        let (was, was_diagnostics) = self
            .before
            .entry(path.to_string())
            .or_insert_with(|| file_hashes(path, original));
        let (after, diagnostics) = file_hashes(path, edited);
        // An error the file already had (an expected failure) doesn't count.
        let new_error = diagnostics.iter().find(|d| {
            d.severity == Severity::Error
                && !was_diagnostics
                    .iter()
                    .any(|w| w.code == d.code && w.message == d.message)
        });
        if let Some(error) = new_error {
            return Verdict::Needed(format!("{}: {}", error.code, first_line(&error.message)));
        }
        compare(was, &after)
    }
}

fn compare(before: &[DeclHash], after: &[DeclHash]) -> Verdict {
    let diff = declhash::compare(before, after, &promise());
    if diff.is_empty() {
        return Verdict::Same(
            diff.proofs_only
                .into_iter()
                .chain(diff.proofs_changed)
                .collect(),
        );
    }
    let mut names: Vec<String> = diff.changed.iter().map(|c| c.name.clone()).collect();
    names.extend(diff.added.iter().map(|n| format!("{n} (added)")));
    names.extend(diff.removed.iter().map(|n| format!("{n} (removed)")));
    Verdict::Changed(names)
}

/// An edited copy of the library, checked by a child process.
struct StdJudge {
    copy: PathBuf,
    before: Vec<DeclHash>,
}

impl Judge for StdJudge {
    fn judge(&mut self, path: &str, original: &str, edited: &str) -> Verdict {
        let target = self.copy.join(path);
        if let Err(e) = std::fs::write(&target, edited) {
            return Verdict::Needed(format!("can't write the copy: {e}"));
        }
        let loaded = library_hashes(&self.copy);
        let _ = std::fs::write(&target, original);
        match loaded {
            Err(report) => Verdict::Needed(
                report
                    .lines()
                    .find(|l| l.contains("error") || l.contains("E-"))
                    .map_or_else(|| first_line(&report), first_line),
            ),
            Ok(after) => compare(&self.before, &after),
        }
    }
}

impl Drop for StdJudge {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.copy);
    }
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

/// A file to try sites in.
struct Target {
    /// As the project, or the library, names it.
    path: String,
    text: String,
}

fn parses(text: &str) -> bool {
    let file = SourceMap::new().add("oracle.sw", text);
    parse_module_within(file, text, DEFAULT_STACK).is_ok()
}

pub(super) fn run(args: &Args) -> ExitCode {
    if args.paths.is_empty() {
        return refused(args.json, "give the files or folders to try".to_string());
    }
    let mut files = Vec::new();
    for p in args.paths {
        if let Err(e) = sw_files(p, &mut files) {
            return refused(args.json, format!("can't read {}: {e}", p.display()));
        }
    }
    let std_root = args
        .std_root
        .map(Path::to_path_buf)
        .or_else(default_std_root);
    // The readings are those the library declares, and any the files do.
    let mut readings = BTreeSet::new();
    if let Some(root) = &std_root {
        let mut library = Vec::new();
        let _ = sw_files(root, &mut library);
        for f in &library {
            if let Ok(text) = std::fs::read_to_string(f) {
                readings.extend(oracle_sites::readings_in(&text));
            }
        }
    }
    if std_root.is_none() && args.half == Half::Builds {
        eprintln!(
            "warning: the library's source isn't here (give --std-root): the `.backward` of its \
             readings won't be found, only the named helpers"
        );
    }
    let mut mode = "project";
    let mut targets = Vec::new();
    let mut judge: Box<dyn Judge> = if args.std {
        mode = "std";
        let Some(root) = std_root else {
            return refused(
                args.json,
                "can't find the library's source: give --std-root".to_string(),
            );
        };
        for f in &files {
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
            targets.push(Target { path, text });
        }
        let before = match library_hashes(&root) {
            Ok(before) => before,
            Err(e) => return refused(args.json, format!("the library doesn't load: {e}")),
        };
        let copy =
            std::env::temp_dir().join(format!("stitchwort-oracle-std-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&copy);
        if let Err(e) = copy_dir(&root, &copy) {
            return refused(args.json, format!("can't copy the library: {e}"));
        }
        Box::new(StdJudge { copy, before })
    } else if args.files {
        mode = "file";
        for f in &files {
            match std::fs::read_to_string(f) {
                Ok(text) => targets.push(Target {
                    path: f.display().to_string(),
                    text,
                }),
                Err(e) => return refused(args.json, format!("can't read {}: {e}", f.display())),
            }
        }
        Box::new(FileJudge::default())
    } else {
        let (project, live) = match super::trial_cmd::load(
            args.project,
            args.cache,
            "try the oracle on",
            "oracle readings src",
        ) {
            Ok(loaded) => loaded,
            Err(messages) => return refused(args.json, messages.join("; ")),
        };
        // A declaration that fails already would look "redundant" (the edit
        // adds no new error), so the project must check as it is.
        let mut live = live;
        let broken: Vec<String> = live
            .answers()
            .iter()
            .flat_map(|(place, file)| {
                file.diagnostics
                    .iter()
                    .filter(|d| d.severity == Severity::Error)
                    .map(move |d| {
                        let path = match place {
                            Place::Program(p) | Place::Library(p) => p,
                        };
                        format!("{path}:{}: {}", d.range[0] + 1, first_line(&d.message))
                    })
            })
            .collect();
        if !broken.is_empty() {
            return refused(
                args.json,
                format!(
                    "the project doesn't check ({}): fix it first",
                    broken.join("; ")
                ),
            );
        }
        for f in &files {
            let Some(path) = relative(f, &project.dir) else {
                return refused(args.json, format!("{} is not in the project", f.display()));
            };
            let Some(text) = live.text(&path) else {
                return refused(
                    args.json,
                    format!("{path} is not one of the project's files"),
                );
            };
            targets.push(Target {
                path,
                text: text.to_string(),
            });
        }
        Box::new(ProjectJudge { live })
    };
    for t in &targets {
        readings.extend(oracle_sites::readings_in(&t.text));
    }

    let started = Instant::now();
    let mut results: Vec<(String, Site, String, Verdict)> = Vec::new();
    // Files that can't be judged as they are (they don't parse or check),
    // each with the reason.
    let mut skipped: Vec<String> = Vec::new();
    'files: for t in &targets {
        if !parses(&t.text) {
            skipped.push(format!("{}: it doesn't parse", t.path));
            continue;
        }
        if let Err(why) = judge.ready(&t.path, &t.text) {
            skipped.push(format!("{}: {why}", t.path));
            continue;
        }
        for site in oracle_sites::find(&t.text, args.half, &readings) {
            if args.limit.is_some_and(|n| results.len() >= n) {
                break 'files;
            }
            let edited = site.apply(&t.text);
            let verdict = if parses(&edited) {
                judge.judge(&t.path, &t.text, &edited)
            } else {
                Verdict::Unparseable
            };
            let excerpt = site.excerpt(&t.text);
            if !args.json {
                println!(
                    "{}:{}:{}: {}: {}",
                    t.path,
                    site.line,
                    site.column,
                    verdict.word(args.half),
                    excerpt
                );
            }
            results.push((t.path.clone(), site, excerpt, verdict));
        }
    }
    drop(judge);
    report(
        args,
        mode,
        &results,
        &skipped,
        started.elapsed().as_secs_f64(),
    )
}

fn report(
    args: &Args,
    mode: &str,
    results: &[(String, Site, String, Verdict)],
    skipped: &[String],
    seconds: f64,
) -> ExitCode {
    let mut counts: BTreeMap<&str, usize> = BTreeMap::new();
    // Per helper: [needed, same, changed, unparseable].
    let mut by_helper: BTreeMap<&str, [usize; 4]> = BTreeMap::new();
    for (_, site, _, verdict) in results {
        *counts.entry(verdict.word(args.half)).or_default() += 1;
        let row = by_helper.entry(site.helper.as_str()).or_default();
        row[match verdict {
            Verdict::Needed(_) => 0,
            Verdict::Same(_) => 1,
            Verdict::Changed(_) => 2,
            Verdict::Unparseable => 3,
        }] += 1;
    }
    let changed = counts.get("changed").copied().unwrap_or(0);
    if args.json {
        let site_json = |(path, site, excerpt, verdict): &(String, Site, String, Verdict)| {
            let detail = match verdict {
                Verdict::Needed(why) => json!(why),
                Verdict::Same(proofs) | Verdict::Changed(proofs) => json!(proofs),
                Verdict::Unparseable => Value::Null,
            };
            json!({
                "file": path,
                "line": site.line,
                "column": site.column,
                "helper": site.helper,
                "text": excerpt,
                "replacement": site.replacement,
                "verdict": verdict.word(args.half),
                "detail": detail,
            })
        };
        let removable: Vec<Value> = results
            .iter()
            .filter(|(_, _, _, v)| matches!(v, Verdict::Same(_)))
            .map(site_json)
            .collect();
        let bad: Vec<Value> = results
            .iter()
            .filter(|(_, _, _, v)| matches!(v, Verdict::Changed(_)))
            .map(site_json)
            .collect();
        let helpers: BTreeMap<&str, Value> = by_helper
            .iter()
            .map(|(h, r)| {
                (
                    *h,
                    json!({ "needed": r[0], "removable": r[1], "changed": r[2], "unparseable": r[3] }),
                )
            })
            .collect();
        print_json(json!({
            "version": 1,
            "half": match args.half { Half::Readings => "readings", Half::Builds => "builds" },
            "mode": mode,
            "promise": "proofs-only",
            "status": if changed == 0 { "clean" } else { "problems" },
            "seconds": (seconds * 10.0).round() / 10.0,
            "summary": {
                "sites": results.len(),
                "needed": counts.get("needed").copied().unwrap_or(0),
                "removable": counts.get("redundant").copied().unwrap_or(0)
                    + counts.get("removable").copied().unwrap_or(0),
                "changed": changed,
                "unparseable": counts.get("unparseable").copied().unwrap_or(0),
                "byHelper": helpers,
            },
            "skippedFiles": skipped,
            "removable": removable,
            "changed": bad,
            "sites": results.iter().map(site_json).collect::<Vec<_>>(),
        }));
    } else {
        println!(
            "{} site(s) in {seconds:.1} s: {}",
            results.len(),
            counts
                .iter()
                .map(|(w, n)| format!("{n} {w}"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        for path in skipped {
            println!("skipped {path}");
        }
        for (helper, r) in &by_helper {
            println!(
                "  {helper}: {} needed, {} removable, {} changed, {} unparseable",
                r[0], r[1], r[2], r[3]
            );
        }
        for (path, site, excerpt, verdict) in results {
            if let Verdict::Changed(names) = verdict {
                println!(
                    "CHANGED MEANING at {path}:{}:{}: {excerpt} moved {}",
                    site.line,
                    site.column,
                    names.join(", ")
                );
            }
        }
    }
    ExitCode::from(if changed == 0 { CLEAN } else { PROBLEMS })
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_driver::declhash::{DeclHash, DeclKind, parse_hash};

    fn decl(kind: DeclKind, name: &str, hash: &str, type_hash: &str, proofless: &str) -> DeclHash {
        DeclHash {
            kind,
            name: name.to_string(),
            hash: parse_hash(hash),
            type_hash: parse_hash(type_hash),
            proofless: parse_hash(proofless),
            uses: Vec::new(),
        }
    }

    fn h(n: u8) -> String {
        format!("{n:02x}").repeat(32)
    }

    #[test]
    fn a_new_proof_keeps_the_meaning_and_a_new_statement_does_not() {
        let was = [
            decl(DeclKind::Theorem, "L.t", &h(1), &h(2), &h(2)),
            decl(DeclKind::Def, "L.d", &h(3), &h(4), &h(5)),
        ];
        // `t` re-proved (hash moved, statement held); `d` embeds a proof.
        let reproved = [
            decl(DeclKind::Theorem, "L.t", &h(9), &h(2), &h(2)),
            decl(DeclKind::Def, "L.d", &h(8), &h(4), &h(5)),
        ];
        assert!(matches!(compare(&was, &reproved), Verdict::Same(_)));
        // `t`'s statement moved.
        let moved = [
            decl(DeclKind::Theorem, "L.t", &h(9), &h(7), &h(7)),
            decl(DeclKind::Def, "L.d", &h(3), &h(4), &h(5)),
        ];
        assert_eq!(
            compare(&was, &moved),
            Verdict::Changed(vec!["L.t".to_string()])
        );
    }
}
