//! `stitchwort rename TARGET NEW-NAME` (SW-2630, docs/proposals/refactoring.md):
//! renames a local, hypothesis, function or theorem of the project.
//!
//! The project is checked, the rename's edits made by
//! [`stitchwort_driver::rename`] and tried on the checked project
//! ([`LiveProject::trial`]). Clean, the files are written. With problems
//! nothing is written, unless `--anyway`: then the edits go in and the
//! problems are listed as what is left to fix by hand (D3467).
//!
//! Exit status: 0 renamed cleanly (or, with `--dry-run`, would be);
//! 1 problems found and nothing written; 2 refused or not understood, nothing
//! written (`--anyway` cannot override this); 3 written with problems left,
//! `--anyway`.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use serde_json::{Value, json};
use stitchwort_cli::project::{DiskFiles, project_sources};
use stitchwort_driver::live::{Edit, LiveProject, Place, Progress, TrialOutcome};
use stitchwort_driver::rename::{RenamePlan, Target};
use stitchwort_syntax::{Severity, SourceMap};

use super::{CacheArgs, locate_project, new_session, use_cache};

pub(super) struct Args<'a> {
    pub target: &'a str,
    pub new_name: &'a str,
    pub anyway: bool,
    pub dry_run: bool,
    pub json: bool,
    pub project: Option<&'a Path>,
    pub cache: &'a CacheArgs,
}

const CLEAN: u8 = 0;
const PROBLEMS: u8 = 1;
const REFUSED: u8 = 2;
const APPLIED_WITH_PROBLEMS: u8 = 3;

pub(super) fn rename(args: &Args) -> ExitCode {
    ExitCode::from(run(args))
}

/// A refusal: said on standard error, or as JSON on standard output.
fn refused(args: &Args, messages: Vec<String>) -> u8 {
    if args.json {
        let refusals: Vec<Value> = messages.iter().map(|m| json!({ "message": m })).collect();
        print_json(json!({
            "version": 1,
            "status": "refused",
            "applied": false,
            "refusals": refusals,
        }));
    } else {
        for m in &messages {
            eprintln!("error: {m}");
        }
    }
    REFUSED
}

fn print_json(value: Value) {
    println!("{}", serde_json::to_string_pretty(&value).expect("JSON"));
}

fn run(args: &Args) -> u8 {
    let Some(project) = locate_project(args.project, "rename in", "rename Foo.bar baz") else {
        return REFUSED;
    };
    let mut session = new_session(true);
    use_cache(&mut session, args.cache, &project.dir);
    session.include_from(std::rc::Rc::new(DiskFiles {
        root: project.dir.clone(),
    }));
    let mut sources = SourceMap::new();
    let files = match project_sources(&project.files, &project.name, &mut sources) {
        Ok(files) => files.into_iter().collect(),
        Err(errors) => {
            let messages = errors.iter().map(|d| d.message.clone()).collect();
            return refused(args, messages);
        }
    };
    let config = std::fs::read_to_string(project.dir.join("stitchwort.yaml")).ok();
    let mut live = LiveProject::new(session, &project.name, config, files);
    while let Ok(Progress::Checked { .. }) = live.step() {}

    let target = parse_target(args.target, &project.dir);
    let plan = match live.rename_plan(&target, args.new_name) {
        Ok(plan) => plan,
        Err(e) => {
            let mut message = e.describe();
            if matches!(
                e,
                stitchwort_driver::rename::RenameError::NoSuchName(_)
                    | stitchwort_driver::rename::RenameError::NothingAt { .. }
            ) && live
                .answers()
                .values()
                .flat_map(|f| &f.diagnostics)
                .any(|d| d.severity == Severity::Error)
            {
                message.push_str(
                    " (the project has errors, which can hide names: run `stitchwort check`)",
                );
            }
            return refused(args, vec![message]);
        }
    };
    let doing = format!("renaming `{}` to `{}`", plan.old, plan.new);
    let trial = match live.trial(&plan.edits, &plan.promise) {
        Ok(TrialOutcome::Checked(trial)) => trial,
        Ok(TrialOutcome::Refused(refusals)) => {
            return refused(args, refusals.iter().map(|r| r.describe(&doing)).collect());
        }
        Err(_) => return refused(args, vec!["the check was cancelled".to_string()]),
    };
    let problems = trial.problems.clone();
    let messages = problems.describe(&doing);
    let clean = problems.is_empty();
    let write = !args.dry_run && (clean || args.anyway);
    let mut written = Vec::new();
    if write {
        let mut paths: Vec<&str> = plan
            .edits
            .iter()
            .filter_map(|e| match &e.place {
                Place::Program(p) => Some(p.as_str()),
                Place::Library(_) => None,
            })
            .collect();
        paths.dedup();
        for path in paths {
            let text = live.text(path).expect("an edited file").to_string();
            let full = path
                .split('/')
                .fold(project.dir.clone(), |dir, part| dir.join(part));
            if let Err(e) = std::fs::write(&full, text) {
                eprintln!("error: can't write {}: {e}", full.display());
                return REFUSED;
            }
            written.push(path.to_string());
        }
    }

    let status = if args.dry_run {
        "dry-run"
    } else if clean {
        "applied"
    } else if args.anyway {
        "applied-with-problems"
    } else {
        "not-applied"
    };
    let code = if clean {
        CLEAN
    } else if write {
        APPLIED_WITH_PROBLEMS
    } else {
        PROBLEMS
    };
    if args.json {
        print_json(result_json(&plan, status, write, &problems, &messages));
    } else {
        print_text(&plan, status, &problems, &messages, &written, args);
    }
    code
}

fn parse_target(text: &str, dir: &Path) -> Target {
    let mut parts = text.rsplitn(3, ':');
    if let (Some(column), Some(line), Some(path)) = (parts.next(), parts.next(), parts.next())
        && let (Ok(line), Ok(column)) = (line.parse::<u32>(), column.parse::<u32>())
        && line >= 1
        && column >= 1
    {
        return Target::At {
            path: project_path(path, dir),
            line: line - 1,
            column: column - 1,
        };
    }
    Target::Name(text.to_string())
}

/// A file as the project names it (relative to its folder, with `/`): the
/// path may be given from the current folder or from the project's.
fn project_path(path: &str, dir: &Path) -> String {
    let given = PathBuf::from(path);
    let from_cwd = given.canonicalize().ok();
    let root = dir.canonicalize().ok();
    if let (Some(full), Some(root)) = (from_cwd, root)
        && let Ok(relative) = full.strip_prefix(&root)
    {
        return relative
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
    }
    path.to_string()
}

fn edit_path(edit: &Edit) -> &str {
    match &edit.place {
        Place::Program(p) | Place::Library(p) => p,
    }
}

fn result_json(
    plan: &RenamePlan,
    status: &str,
    written: bool,
    problems: &stitchwort_driver::live::Problems,
    messages: &[String],
) -> Value {
    let edits: Vec<Value> = plan
        .edits
        .iter()
        .map(|e| {
            json!({
                "file": edit_path(e),
                "line": e.range[0] + 1,
                "column": e.range[1] + 1,
                "endLine": e.range[2] + 1,
                "endColumn": e.range[3] + 1,
                "newText": e.new_text,
            })
        })
        .collect();
    let mut list = Vec::new();
    for (d, message) in problems.diagnostics.iter().zip(messages) {
        list.push(json!({
            "kind": match d.severity { Severity::Error => "error", _ => "warning" },
            "file": d.path,
            "line": d.range[0] + 1,
            "column": d.range[1] + 1,
            "declaration": d.declaration,
            "code": d.code,
            "message": message,
        }));
    }
    for (c, message) in problems
        .changed
        .iter()
        .zip(&messages[problems.diagnostics.len()..])
    {
        list.push(json!({
            "kind": "changed-meaning",
            "file": c.path,
            "line": c.range.map(|r| r[0] + 1),
            "column": c.range.map(|r| r[1] + 1),
            "declaration": c.name,
            "uses": c.uses,
            "message": message,
        }));
    }
    json!({
        "version": 1,
        "status": status,
        "applied": written,
        "name": plan.name,
        "kind": plan.kind,
        "old": plan.old,
        "new": plan.new,
        "edits": edits,
        "problems": list,
        "refusals": [],
    })
}

fn print_text(
    plan: &RenamePlan,
    status: &str,
    problems: &stitchwort_driver::live::Problems,
    messages: &[String],
    written: &[String],
    args: &Args,
) {
    let places = plan.edits.len();
    let plural = |n: usize, one: &str, many: &str| {
        if n == 1 {
            one.to_string()
        } else {
            many.to_string()
        }
    };
    let mut files: Vec<&str> = plan.edits.iter().map(edit_path).collect();
    files.dedup();
    let summary = format!(
        "`{}` to `{}`: {places} {} in {} {}",
        plan.old,
        plan.new,
        plural(places, "place", "places"),
        files.len(),
        plural(files.len(), "file", "files"),
    );
    match status {
        "applied" => println!("renamed {summary}"),
        "applied-with-problems" => println!("renamed {summary}, with problems left to fix"),
        "dry-run" => println!("would rename {summary}"),
        _ => println!("did not rename {summary}"),
    }
    if status == "dry-run" || args.dry_run {
        for e in &plan.edits {
            println!("  {}:{}:{}", edit_path(e), e.range[0] + 1, e.range[1] + 1);
        }
    } else if !written.is_empty() {
        for file in written {
            println!("  wrote {file}");
        }
    }
    let _ = problems;
    if !messages.is_empty() {
        println!();
        println!(
            "{} {}:",
            messages.len(),
            plural(messages.len(), "problem", "problems")
        );
        for m in messages {
            println!("  {m}");
        }
        if status == "not-applied" || (status == "dry-run") {
            println!();
            println!("nothing was written; to rename anyway and fix these by hand, add `--anyway`");
        }
    }
}
