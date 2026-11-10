//! `stitchwort trial-edits EDITS.json` and `stitchwort hash` (SW-2648,
//! SW-2647): developer tools for sweeps that rewrite many declarations and
//! must show each kept its meaning (docs/proposals/theorem-binders.md §5).
//!
//! `trial-edits` tries arbitrary edits on the checked project
//! ([`LiveProject::trial`]) and reports the new diagnostics and the
//! declarations whose content hash moved, JSON with `--json`. It writes
//! nothing unless `--apply`, and then only if nothing was found (or with
//! `--anyway`). With `--std-dir DIR` it checks an edited copy of the
//! standard library instead: this process loads `DIR`, a child process
//! loads the library as it was (`--std-before`, else what the environment
//! would pick), and every declaration's hashes are compared, since a process
//! reads the library only once.
//!
//! Exit status: 0 nothing found; 1 problems found; 2 refused or not
//! understood.

use std::collections::BTreeMap;
use std::path::Path;
use std::process::{Command, ExitCode};

use serde_json::{Value, json};
use stitchwort_cli::project::{DiskFiles, project_sources};
use stitchwort_driver::declhash::{self, DeclHash, DeclKind, HashDiff};
use stitchwort_driver::live::{Edit, LiveProject, Place, Progress, Promise, TrialOutcome};
use stitchwort_syntax::{Severity, SourceMap};

use super::{CacheArgs, STACK, locate_project, new_session, use_cache};

const CLEAN: u8 = 0;
const PROBLEMS: u8 = 1;
const REFUSED: u8 = 2;

pub(super) struct TrialArgs<'a> {
    pub edits: Option<&'a Path>,
    pub same_statement: bool,
    pub apply: bool,
    pub anyway: bool,
    pub json: bool,
    pub std_before: Option<&'a Path>,
    /// Whether `--std-dir` was given: this process reads the edited library.
    pub std_mode: bool,
    pub project: Option<&'a Path>,
    pub cache: &'a CacheArgs,
}

pub(super) struct HashArgs<'a> {
    pub names: &'a [String],
    pub std: bool,
    pub json: bool,
    /// With `json`: list what each definition mentions.
    pub uses: bool,
    pub project: Option<&'a Path>,
    pub cache: &'a CacheArgs,
}

fn promise(same_statement: bool) -> Promise {
    let renames = BTreeMap::new();
    if same_statement {
        Promise::SameStatement { renames }
    } else {
        Promise::SameMeaning { renames }
    }
}

fn promise_name(same_statement: bool) -> &'static str {
    if same_statement {
        "same-statement"
    } else {
        "same-meaning"
    }
}

fn print_json(value: Value) {
    println!("{}", serde_json::to_string_pretty(&value).expect("JSON"));
}

/// A refusal: on standard error, or as JSON on standard output.
fn refused(json: bool, mode: &str, messages: Vec<String>) -> ExitCode {
    if json {
        let refusals: Vec<Value> = messages.iter().map(|m| json!({ "message": m })).collect();
        print_json(json!({
            "version": 1,
            "mode": mode,
            "status": "refused",
            "applied": false,
            "diagnostics": [],
            "changed": [],
            "refusals": refusals,
        }));
    } else {
        for m in &messages {
            eprintln!("error: {m}");
        }
    }
    ExitCode::from(REFUSED)
}

/// Checks the project fully.
pub(super) fn load(
    project_flag: Option<&Path>,
    cache: &CacheArgs,
    what: &str,
    example: &str,
) -> Result<(super::Project, LiveProject), Vec<String>> {
    let Some(project) = locate_project(project_flag, what, example) else {
        return Err(Vec::new());
    };
    let mut session = new_session(true);
    use_cache(&mut session, cache, &project.dir);
    session.include_from(std::rc::Rc::new(DiskFiles {
        root: project.dir.clone(),
    }));
    let mut sources = SourceMap::new();
    let files = match project_sources(&project.files, &project.name, &mut sources) {
        Ok(files) => files.into_iter().collect(),
        Err(errors) => return Err(errors.iter().map(|d| d.message.clone()).collect()),
    };
    let config = std::fs::read_to_string(project.dir.join("stitchwort.yaml")).ok();
    let mut live = LiveProject::new(session, &project.name, config, files);
    while let Ok(Progress::Checked { .. }) = live.step() {}
    Ok((project, live))
}

pub(super) fn trial_edits(args: &TrialArgs) -> ExitCode {
    if args.std_mode {
        if args.apply || args.edits.is_some() {
            return refused(
                args.json,
                "std",
                vec![
                    "with --std-dir the edits are the edited copy itself: give no edits file \
                     and no --apply"
                        .to_string(),
                ],
            );
        }
        return std_trial(args);
    }
    if args.std_before.is_some() {
        return refused(
            args.json,
            "project",
            vec!["--std-before goes with --std-dir".to_string()],
        );
    }
    let mode = "project";
    let Some(edits_path) = args.edits else {
        return refused(
            args.json,
            mode,
            vec!["give the edits file, or --std-dir for an edited library".to_string()],
        );
    };
    let (project, mut live) = match load(
        args.project,
        args.cache,
        "try edits on",
        "trial-edits edits.json",
    ) {
        Ok(loaded) => loaded,
        Err(messages) if messages.is_empty() => return ExitCode::from(REFUSED),
        Err(messages) => return refused(args.json, mode, messages),
    };
    let edits = match read_edits(edits_path, &live, &project.dir) {
        Ok(edits) => edits,
        Err(message) => return refused(args.json, mode, vec![message]),
    };
    let doing = "the edits";
    let trial = match live.trial(&edits, &promise(args.same_statement)) {
        Ok(TrialOutcome::Checked(trial)) => trial,
        Ok(TrialOutcome::Refused(refusals)) => {
            return refused(
                args.json,
                mode,
                refusals.iter().map(|r| r.describe(doing)).collect(),
            );
        }
        Err(_) => return refused(args.json, mode, vec!["the check was cancelled".to_string()]),
    };
    let problems = trial.problems.clone();
    let proofs_changed = trial.proofs_changed.clone();
    let messages = problems.describe(doing);
    let clean = problems.is_empty();
    let write = args.apply && (clean || args.anyway);
    let mut written = Vec::new();
    if write {
        let mut paths: Vec<&str> = edits
            .iter()
            .filter_map(|e| match &e.place {
                Place::Program(p) => Some(p.as_str()),
                Place::Library(_) => None,
            })
            .collect();
        paths.sort();
        paths.dedup();
        for path in paths {
            let text = live.text(path).expect("an edited file").to_string();
            let full = path
                .split('/')
                .fold(project.dir.clone(), |dir, part| dir.join(part));
            if let Err(e) = std::fs::write(&full, text) {
                eprintln!("error: can't write {}: {e}", full.display());
                return ExitCode::from(REFUSED);
            }
            written.push(path.to_string());
        }
    }
    // Nothing is left applied in the checked project that isn't on disk.
    let _ = live.restore(trial);

    if args.json {
        let diagnostics: Vec<Value> = problems
            .diagnostics
            .iter()
            .map(|d| {
                json!({
                    "severity": match d.severity { Severity::Error => "error", _ => "warning" },
                    "file": d.path,
                    "line": d.range[0] + 1,
                    "column": d.range[1] + 1,
                    "declaration": d.declaration,
                    "code": d.code,
                    "message": d.message,
                })
            })
            .collect();
        let changed: Vec<Value> = problems
            .changed
            .iter()
            .map(|c| {
                json!({
                    "namespace": c.namespace,
                    "name": c.name,
                    "file": c.path,
                    "line": c.range.map(|r| r[0] + 1),
                    "column": c.range.map(|r| r[1] + 1),
                    "uses": c.uses,
                })
            })
            .collect();
        print_json(json!({
            "version": 1,
            "mode": mode,
            "promise": promise_name(args.same_statement),
            "status": if clean { "clean" } else { "problems" },
            "applied": write,
            "written": written,
            "diagnostics": diagnostics,
            "changed": changed,
            "proofsChanged": proofs_changed,
            "messages": messages,
            "refusals": [],
        }));
    } else {
        for m in &messages {
            println!("{m}");
        }
        if !proofs_changed.is_empty() {
            println!(
                "{} proof(s) changed with the statement kept",
                proofs_changed.len()
            );
        }
        if clean {
            println!("nothing found: every declaration is as promised");
        }
        for file in &written {
            println!("wrote {file}");
        }
        if !clean && !write {
            println!("nothing was written");
        }
    }
    ExitCode::from(if clean { CLEAN } else { PROBLEMS })
}

/// The edits file: a list of edits, or an object with an `edits` list (as
/// `rename --dry-run --json` prints). An edit is `{file, line, column,
/// endLine, endColumn, newText}` (from 1, columns in UTF-16 units), or
/// `{file, text}` to replace the whole file.
fn read_edits(path: &Path, live: &LiveProject, dir: &Path) -> Result<Vec<Edit>, String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("can't read {}: {e}", path.display()))?;
    let value: Value =
        serde_json::from_str(&text).map_err(|e| format!("{}: not JSON: {e}", path.display()))?;
    let list = match &value {
        Value::Array(list) => list,
        Value::Object(map) => map
            .get("edits")
            .and_then(Value::as_array)
            .ok_or("the edits file is an object without an `edits` list")?,
        _ => return Err("the edits file is neither a list nor an object".to_string()),
    };
    let mut edits = Vec::new();
    for (i, item) in list.iter().enumerate() {
        let bad = |what: &str| format!("edit {}: {what}", i + 1);
        let file = item
            .get("file")
            .and_then(Value::as_str)
            .ok_or_else(|| bad("no `file`"))?;
        let file = super::rename_cmd::project_path(file, dir);
        let place = Place::Program(file.clone());
        if let Some(new_text) = item.get("text").and_then(Value::as_str) {
            let old = live
                .text(&file)
                .ok_or_else(|| bad(&format!("`{file}` is not a file of the project")))?;
            let lines = old.split('\n').count() as u32 - 1;
            let last = old.rsplit('\n').next().unwrap_or("");
            let column = last.encode_utf16().count() as u32;
            edits.push(Edit {
                place,
                range: [0, 0, lines, column],
                new_text: new_text.to_string(),
            });
            continue;
        }
        let number = |key: &str| {
            item.get(key)
                .and_then(Value::as_u64)
                .filter(|n| *n >= 1)
                .map(|n| n as u32 - 1)
                .ok_or_else(|| bad(&format!("no `{key}` (a number from 1)")))
        };
        let new_text = item
            .get("newText")
            .and_then(Value::as_str)
            .ok_or_else(|| bad("no `newText` (or `text` for a whole file)"))?;
        edits.push(Edit {
            place,
            range: [
                number("line")?,
                number("column")?,
                number("endLine")?,
                number("endColumn")?,
            ],
            new_text: new_text.to_string(),
        });
    }
    Ok(edits)
}

fn decl_json(d: &DeclHash, uses: bool) -> Value {
    let mut v = json!({
        "kind": d.kind.word(),
        "name": d.name,
        "hash": d.hash.map(|h| h.hex()),
        "typeHash": d.type_hash.map(|h| h.hex()),
    });
    if uses && !d.uses.is_empty() {
        v["uses"] = json!(d.uses);
    }
    v
}

pub(super) fn decl_from_json(v: &Value) -> Option<DeclHash> {
    let kind = match v.get("kind")?.as_str()? {
        "data" => DeclKind::Data,
        "def" => DeclKind::Def,
        "theorem" => DeclKind::Theorem,
        _ => return None,
    };
    let hash = |key: &str| v.get(key)?.as_str().and_then(declhash::parse_hash);
    Some(DeclHash {
        kind,
        name: v.get("name")?.as_str()?.to_string(),
        hash: hash("hash"),
        type_hash: hash("typeHash"),
        uses: v
            .get("uses")
            .and_then(Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(|u| u.as_str().map(str::to_string))
                    .collect()
            })
            .unwrap_or_default(),
    })
}

/// `--std-dir`: the edited library (this process) against the library as it
/// was (a child process).
fn std_trial(args: &TrialArgs) -> ExitCode {
    let mode = "std";
    let after = match declhash::library_hashes(STACK) {
        Ok(after) => after,
        Err(report) => {
            // An edited library that doesn't load is the new diagnostic.
            return std_report(args, &HashDiff::default(), Some(report), false);
        }
    };
    let exe = match std::env::current_exe() {
        Ok(exe) => exe,
        Err(e) => return refused(args.json, mode, vec![format!("can't find myself: {e}")]),
    };
    let mut child = Command::new(exe);
    if let Some(dir) = args.std_before {
        child.arg("--std-dir").arg(dir);
    }
    child.args(["hash", "--std", "--json"]);
    // Whatever the edited run was told, the child decides for itself.
    let output = match child.output() {
        Ok(output) => output,
        Err(e) => {
            return refused(
                args.json,
                mode,
                vec![format!("can't run the original: {e}")],
            );
        }
    };
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return refused(
            args.json,
            mode,
            vec![format!(
                "the library as it was doesn't load: {}",
                stderr.trim()
            )],
        );
    }
    let before: Option<Vec<DeclHash>> = serde_json::from_slice::<Value>(&output.stdout)
        .ok()
        .and_then(|v| {
            v.get("declarations")?
                .as_array()?
                .iter()
                .map(decl_from_json)
                .collect()
        });
    let Some(before) = before else {
        return refused(
            args.json,
            mode,
            vec!["can't read the original library's hashes".to_string()],
        );
    };
    let diff = declhash::compare(&before, &after, &promise(args.same_statement));
    std_report(args, &diff, None, true)
}

fn std_report(
    args: &TrialArgs,
    diff: &HashDiff,
    load_error: Option<String>,
    loaded: bool,
) -> ExitCode {
    let clean = diff.is_empty() && load_error.is_none();
    if args.json {
        let changed: Vec<Value> = diff
            .changed
            .iter()
            .map(|c| {
                json!({
                    "name": c.name,
                    "kind": c.kind.word(),
                    "was": c.was.map(|h| h.hex()),
                    "now": c.now.map(|h| h.hex()),
                })
            })
            .collect();
        let diagnostics: Vec<Value> = load_error
            .iter()
            .map(|m| json!({ "severity": "error", "message": m }))
            .collect();
        print_json(json!({
            "version": 1,
            "mode": "std",
            "promise": promise_name(args.same_statement),
            "status": if clean { "clean" } else { "problems" },
            "applied": false,
            "diagnostics": diagnostics,
            "changed": changed,
            "proofsChanged": diff.proofs_changed,
            "added": diff.added,
            "removed": diff.removed,
            "reordered": diff.reordered,
            "refusals": [],
        }));
    } else {
        if let Some(report) = &load_error {
            println!("the edited library doesn't load:\n{report}");
        }
        for c in &diff.changed {
            println!("changed: {} {}", c.kind.word(), c.name);
        }
        for n in &diff.added {
            println!("added: {n}");
        }
        for n in &diff.removed {
            println!("removed: {n}");
        }
        if !diff.proofs_changed.is_empty() {
            println!(
                "{} proof(s) changed with the statement kept",
                diff.proofs_changed.len()
            );
        }
        if clean && loaded {
            println!("nothing found: every declaration is as promised");
        }
    }
    ExitCode::from(if clean { CLEAN } else { PROBLEMS })
}

/// `stitchwort hash`: the content hashes of declarations.
pub(super) fn hash(args: &HashArgs) -> ExitCode {
    let all = if args.std {
        match declhash::library_hashes(STACK) {
            Ok(all) => all,
            Err(report) => {
                eprintln!("error: the library doesn't load:\n{report}");
                return ExitCode::from(REFUSED);
            }
        }
    } else {
        match load(args.project, args.cache, "hash in", "hash Foo.bar") {
            Ok((_, live)) => live.declaration_hashes(),
            Err(messages) => {
                for m in &messages {
                    eprintln!("error: {m}");
                }
                return ExitCode::from(REFUSED);
            }
        }
    };
    let wanted = |d: &DeclHash| {
        args.names.is_empty()
            || args.names.iter().any(|n| {
                d.name == *n
                    || d.name
                        .strip_prefix(n.as_str())
                        .is_some_and(|rest| rest.starts_with('.'))
            })
    };
    let shown: Vec<&DeclHash> = all.iter().filter(|d| wanted(d)).collect();
    let missing: Vec<&String> = args
        .names
        .iter()
        .filter(|n| !all.iter().any(|d| d.name == **n))
        .collect();
    if args.json {
        print_json(json!({
            "version": 1,
            "declarations": shown.iter().map(|d| decl_json(d, args.uses)).collect::<Vec<_>>(),
            "missing": missing,
        }));
    } else {
        for d in &shown {
            println!(
                "{} {} {} {}",
                declhash::show(d.hash),
                declhash::show(d.type_hash),
                d.kind.word(),
                d.name
            );
        }
        for n in &missing {
            eprintln!("error: no declaration `{n}`");
        }
    }
    ExitCode::from(if missing.is_empty() { CLEAN } else { PROBLEMS })
}
