//! `stitchwort dev breaks` (SW-3226): the one-line-break oracle of
//! docs/proposals/syntax-error-recovery.md §6.
//!
//! Every file under the paths that checks cleanly is broken one line at a
//! time, each break on its own, two ways: the line's last token dropped,
//! and a stray `)` put before its middle token. Lines of a namespace line or
//! an import are left alone: the oracle is about declarations. A break that
//! still parses isn't a syntax error, so it is skipped. The broken file is
//! checked, and every error in it that the parser didn't report is a
//! *false* error: the declaration was correct, so the syntax error is the
//! only thing wrong with it.
//!
//! Each break is counted under the recovery point the parser used for the
//! broken declaration (its first, [`RecoveryPoint`]), or, when it didn't
//! recover, under `kept signature` (a definition whose header parsed) or
//! `whole` (the declaration failed whole).
//!
//! The checking is `check`'s: in a project (the default) incrementally on
//! the checked project, the edited file's diagnostics; with `--files` each
//! file on its own; with `--std` a child process checks the edited file in
//! a copy of the library (`check --std`, with the check cache for the files
//! it needs).
//!
//! Exit status: 0 the run finished; 2 refused.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::time::Instant;

use serde_json::{Value, json};
use stitchwort_cli::project::DiskFiles;
use stitchwort_driver::driver::Session;
use stitchwort_driver::live::{LiveProject, Place, Progress};
use stitchwort_syntax::tree::NodeKind;
use stitchwort_syntax::{DEFAULT_STACK, Severity, SourceMap, parse_module_recovering, parse_tree};

use super::CacheArgs;
use super::sweep_cmd::{copy_dir, default_std_root, relative, sw_files};

const DONE: u8 = 0;
const REFUSED: u8 = 2;

pub(super) struct Args<'a> {
    pub paths: &'a [PathBuf],
    pub std: bool,
    pub files: bool,
    pub std_root: Option<&'a Path>,
    /// Try at most this many breaks, in file and line order.
    pub limit: Option<usize>,
    /// How many of the worst breaks to list.
    pub worst: usize,
    pub json: bool,
    pub project: Option<&'a Path>,
    pub cache: &'a CacheArgs,
}

/// An error a check reported: its code, its line (from 1) and its message's
/// first line.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Reported {
    code: String,
    line: u32,
    message: String,
}

/// Checks a file's text and gives its errors.
trait Checker {
    fn errors(&mut self, path: &str, text: &str) -> Result<Vec<Reported>, String>;
    /// Puts the file back as it was, after a break.
    fn restore(&mut self, _path: &str, _text: &str) {}
}

fn first_line(message: &str) -> String {
    message.lines().next().unwrap_or("").trim().to_string()
}

/// Each file on its own, as `check FILE` loads it.
struct FileChecker;

impl Checker for FileChecker {
    fn errors(&mut self, path: &str, text: &str) -> Result<Vec<Reported>, String> {
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
        let diagnostics = match session.load_file(path, text, None) {
            Ok(_) => Vec::new(),
            Err(diagnostics) => diagnostics,
        };
        Ok(diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .map(|d| Reported {
                code: d.code.to_string(),
                line: d
                    .primary_span()
                    .map_or(0, |s| line_of(text, s.start as usize)),
                message: first_line(&d.message),
            })
            .collect())
    }
}

/// A project, checked incrementally: the edited file's errors.
struct ProjectChecker {
    live: LiveProject,
}

impl ProjectChecker {
    fn settle(&mut self) -> Result<(), String> {
        loop {
            match self.live.step() {
                Ok(Progress::Done | Progress::Checked { done: true, .. }) => return Ok(()),
                Ok(Progress::Checked { .. }) => {}
                Err(_) => return Err("the check was cancelled".to_string()),
            }
        }
    }
}

impl Checker for ProjectChecker {
    fn errors(&mut self, path: &str, text: &str) -> Result<Vec<Reported>, String> {
        self.live.set_text(path, Some(text.to_string()));
        self.settle()?;
        let answers = self.live.answers();
        let Some(file) = answers.get(&Place::Program(path.to_string())) else {
            return Ok(Vec::new());
        };
        Ok(file
            .diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .map(|d| Reported {
                code: d.code.to_string(),
                line: d.range[0] + 1,
                message: first_line(&d.message),
            })
            .collect())
    }

    fn restore(&mut self, path: &str, text: &str) {
        self.live.set_text(path, Some(text.to_string()));
        let _ = self.settle();
        let _ = self.live.answers();
    }
}

/// An edited copy of the library, a file of which a child process checks.
struct StdChecker {
    copy: PathBuf,
    cache_dir: Option<PathBuf>,
}

impl Checker for StdChecker {
    fn errors(&mut self, path: &str, text: &str) -> Result<Vec<Reported>, String> {
        let target = self.copy.join(path);
        let original = std::fs::read_to_string(&target).map_err(|e| e.to_string())?;
        std::fs::write(&target, text).map_err(|e| format!("can't write the copy: {e}"))?;
        let exe = std::env::current_exe().map_err(|e| format!("can't find myself: {e}"))?;
        let mut command = Command::new(exe);
        command
            .arg("--std-dir")
            .arg(&self.copy)
            .args(["check", "--std", path]);
        match &self.cache_dir {
            Some(dir) => command.arg("--cache-dir").arg(dir),
            None => command.arg("--no-cache"),
        };
        let output = command.output();
        let _ = std::fs::write(&target, original);
        let output = output.map_err(|e| format!("can't run the check: {e}"))?;
        Ok(rendered_errors(
            &String::from_utf8_lossy(&output.stderr),
            path,
        ))
    }
}

impl Drop for StdChecker {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.copy);
    }
}

/// The errors in `check`'s rendered report that are in the file at `path`
/// (`[E-CODE] Error: message`, then `╭─[ dir/path:line:column ]`).
fn rendered_errors(report: &str, path: &str) -> Vec<Reported> {
    let mut out = Vec::new();
    let mut lines = report.lines().peekable();
    while let Some(line) = lines.next() {
        let Some(rest) = line.strip_prefix('[') else {
            continue;
        };
        let Some((code, rest)) = rest.split_once("] Error: ") else {
            continue;
        };
        let message = rest.trim().to_string();
        let Some(place) = lines.next() else { break };
        let Some(start) = place.find("─[ ") else {
            continue;
        };
        let place = place[start + "─[ ".len()..].trim_end_matches([' ', ']']);
        let mut parts = place.rsplitn(3, ':');
        let (_, line_number, file) = (parts.next(), parts.next(), parts.next());
        if !file.is_some_and(|f| f.ends_with(path)) {
            continue;
        }
        out.push(Reported {
            code: code.to_string(),
            line: line_number.and_then(|n| n.parse().ok()).unwrap_or(0),
            message,
        });
    }
    out
}

/// The line (from 1) of byte `at` of `text`.
fn line_of(text: &str, at: usize) -> u32 {
    text[..at.min(text.len())].matches('\n').count() as u32 + 1
}

/// How a line is broken.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum How {
    /// Its last token dropped.
    DropLast,
    /// `)` put before its middle token.
    StrayParen,
}

impl How {
    fn word(self) -> &'static str {
        match self {
            How::DropLast => "drop-last",
            How::StrayParen => "stray-paren",
        }
    }
}

/// One break: a line of a file broken one way.
struct Break {
    line: u32,
    how: How,
    edited: String,
}

/// Every break of `text`'s declarations' lines, in line order.
fn breaks(text: &str) -> Vec<Break> {
    let file = SourceMap::new().add("breaks.sw", text);
    let tree = parse_tree(file, text, DEFAULT_STACK);
    let tokens = tree.tokens();
    // The token ranges of each line, for the declarations' tokens only.
    let mut lines: BTreeMap<u32, Vec<usize>> = BTreeMap::new();
    for root in tree.decls() {
        if matches!(root.kind(), NodeKind::Namespace | NodeKind::Import) {
            continue;
        }
        for i in root.token_range() {
            lines
                .entry(line_of(text, tokens[i].span.start as usize))
                .or_default()
                .push(i);
        }
    }
    let mut out = Vec::new();
    for (line, on_line) in lines {
        let last = tokens[*on_line.last().expect("a line has a token")].span;
        let mut edited = String::with_capacity(text.len());
        edited.push_str(&text[..last.start as usize]);
        edited.push_str(&text[last.end as usize..]);
        out.push(Break {
            line,
            how: How::DropLast,
            edited,
        });
        if on_line.len() >= 2 {
            let middle = tokens[on_line[on_line.len() / 2]].span.start as usize;
            let mut edited = String::with_capacity(text.len() + 2);
            edited.push_str(&text[..middle]);
            edited.push_str(") ");
            edited.push_str(&text[middle..]);
            out.push(Break {
                line,
                how: How::StrayParen,
                edited,
            });
        }
    }
    out
}

/// What the parser made of a broken text: its errors (code and line), and
/// the point that recovered the declaration holding `line`.
fn parsed(text: &str, line: u32) -> (Vec<(String, u32)>, &'static str) {
    let file = SourceMap::new().add("breaks.sw", text);
    let (_, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
    let errors = errors
        .iter()
        .map(|d| {
            let at = d.primary_span().map_or(0, |s| s.start as usize);
            (d.code.to_string(), line_of(text, at))
        })
        .collect();
    let tree = parse_tree(file, text, DEFAULT_STACK);
    let tokens = tree.tokens();
    let mut point = "whole";
    for root in tree.decls() {
        let range = root.token_range();
        let (Some(first), Some(last)) = (tokens.get(range.start), range.end.checked_sub(1)) else {
            continue;
        };
        let (from, to) = (
            line_of(text, first.span.start as usize),
            line_of(text, tokens[last].span.end as usize),
        );
        if !(from <= line && line <= to) {
            continue;
        }
        point = match root.recoveries().first() {
            Some(recovery) => recovery.point.label(),
            None if root.signature_kept() => "kept signature",
            None if root.kind() == NodeKind::Error => "whole",
            None => "none",
        };
        break;
    }
    (errors, point)
}

/// What became of a break.
struct Outcome {
    path: String,
    line: u32,
    how: How,
    point: &'static str,
    /// The errors besides the syntax errors.
    false_errors: Vec<Reported>,
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

pub(super) fn run(args: &Args) -> ExitCode {
    if args.paths.is_empty() {
        return refused(args.json, "give the files or folders to break".to_string());
    }
    let mut files = Vec::new();
    for p in args.paths {
        if let Err(e) = sw_files(p, &mut files) {
            return refused(args.json, format!("can't read {}: {e}", p.display()));
        }
    }
    // Each file, as the checker names it, and its text.
    let mut targets: Vec<(String, String)> = Vec::new();
    let mut checker: Box<dyn Checker> = if args.std {
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
        for f in &files {
            let Some(path) = relative(f, &root) else {
                return refused(
                    args.json,
                    format!("{} is not in {}", f.display(), root.display()),
                );
            };
            match std::fs::read_to_string(f) {
                Ok(text) => targets.push((path, text)),
                Err(e) => return refused(args.json, format!("can't read {}: {e}", f.display())),
            }
        }
        let copy =
            std::env::temp_dir().join(format!("stitchwort-breaks-std-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&copy);
        if let Err(e) = copy_dir(&root, &copy) {
            return refused(args.json, format!("can't copy the library: {e}"));
        }
        let cache_dir = if args.cache.no_cache {
            None
        } else {
            Some(
                args.cache
                    .cache_dir
                    .clone()
                    .unwrap_or_else(|| PathBuf::from(".stitchwort/cache")),
            )
        };
        Box::new(StdChecker { copy, cache_dir })
    } else if args.files {
        for f in &files {
            match std::fs::read_to_string(f) {
                Ok(text) => targets.push((f.display().to_string(), text)),
                Err(e) => return refused(args.json, format!("can't read {}: {e}", f.display())),
            }
        }
        Box::new(FileChecker)
    } else {
        let (project, live) = match super::trial_cmd::load(
            args.project,
            args.cache,
            "break lines in",
            "dev breaks src",
        ) {
            Ok(loaded) => loaded,
            Err(messages) => return refused(args.json, messages.join("; ")),
        };
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
            targets.push((path, text.to_string()));
        }
        Box::new(ProjectChecker { live })
    };

    let started = Instant::now();
    let mut outcomes: Vec<Outcome> = Vec::new();
    // Breaks that left text that still parses, which aren't syntax errors.
    let mut still_parse = 0usize;
    // Breaks whose check reported no error at all, so it didn't see the
    // syntax error: a fault of the tool's if ever counted.
    let mut unseen = 0usize;
    // Files that can't be broken as they are, each with the reason.
    let mut skipped: Vec<String> = Vec::new();
    'files: for (path, text) in &targets {
        match checker.errors(path, text) {
            Err(why) => {
                skipped.push(format!("{path}: {why}"));
                continue;
            }
            Ok(errors) if !errors.is_empty() => {
                let e = &errors[0];
                skipped.push(format!(
                    "{path}: it doesn't check as it is: {} (line {}): {}",
                    e.code, e.line, e.message
                ));
                continue;
            }
            Ok(_) => {}
        }
        for b in breaks(text) {
            if args.limit.is_some_and(|n| outcomes.len() >= n) {
                break 'files;
            }
            let (syntax, point) = parsed(&b.edited, b.line);
            if syntax.is_empty() {
                still_parse += 1;
                continue;
            }
            let reported = match checker.errors(path, &b.edited) {
                Ok(reported) => reported,
                Err(why) => vec![Reported {
                    code: "CHECK-FAILED".to_string(),
                    line: b.line,
                    message: why,
                }],
            };
            checker.restore(path, text);
            if !reported.iter().any(|r| r.code.starts_with("E-")) {
                unseen += 1;
                if !args.json {
                    println!("{path}:{}: {}: no error reported", b.line, b.how.word());
                }
            }
            let false_errors: Vec<Reported> = reported
                .into_iter()
                .filter(|r| {
                    !syntax
                        .iter()
                        .any(|(code, line)| *code == r.code && *line == r.line)
                })
                .collect();
            if !args.json && !false_errors.is_empty() {
                let e = &false_errors[0];
                println!(
                    "{path}:{}: {} ({point}): {} false: {} (line {}): {}",
                    b.line,
                    b.how.word(),
                    false_errors.len(),
                    e.code,
                    e.line,
                    e.message
                );
            }
            outcomes.push(Outcome {
                path: path.clone(),
                line: b.line,
                how: b.how,
                point,
                false_errors,
            });
        }
    }
    drop(checker);
    report(
        args,
        &outcomes,
        (still_parse, unseen),
        &skipped,
        started.elapsed().as_secs_f64(),
    )
}

fn report(
    args: &Args,
    outcomes: &[Outcome],
    (still_parse, unseen): (usize, usize),
    skipped: &[String],
    seconds: f64,
) -> ExitCode {
    // Per point: breaks, and those with a false error.
    let mut by_point: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    // Per code of a false error: how many breaks gave one.
    let mut by_code: BTreeMap<&str, usize> = BTreeMap::new();
    for o in outcomes {
        let row = by_point.entry(o.point).or_default();
        row.0 += 1;
        row.1 += usize::from(!o.false_errors.is_empty());
        let mut codes: Vec<&str> = o.false_errors.iter().map(|e| e.code.as_str()).collect();
        codes.dedup();
        for code in codes {
            *by_code.entry(code).or_default() += 1;
        }
    }
    let mut worst: Vec<&Outcome> = outcomes
        .iter()
        .filter(|o| !o.false_errors.is_empty())
        .collect();
    worst.sort_by_key(|o| std::cmp::Reverse(o.false_errors.len()));
    worst.truncate(args.worst);
    let rate = |(breaks, bad): (usize, usize)| {
        if breaks == 0 {
            0.0
        } else {
            100.0 * bad as f64 / breaks as f64
        }
    };
    let total = outcomes.len();
    let bad = outcomes
        .iter()
        .filter(|o| !o.false_errors.is_empty())
        .count();
    if args.json {
        let outcome_json = |o: &Outcome| {
            json!({
                "file": o.path,
                "line": o.line,
                "how": o.how.word(),
                "point": o.point,
                "falseErrors": o.false_errors.iter().map(|e| json!({
                    "code": e.code, "line": e.line, "message": e.message,
                })).collect::<Vec<_>>(),
            })
        };
        print_json(json!({
            "version": 1,
            "status": "done",
            "seconds": (seconds * 10.0).round() / 10.0,
            "breaks": total,
            "withFalseErrors": bad,
            "stillParse": still_parse,
            "unseen": unseen,
            "byPoint": by_point.iter().map(|(p, r)| (p.to_string(), json!({
                "breaks": r.0,
                "withFalseErrors": r.1,
                "percent": (rate(*r) * 100.0).round() / 100.0,
            }))).collect::<serde_json::Map<_, _>>(),
            "byCode": by_code,
            "skippedFiles": skipped,
            "worst": worst.iter().map(|o| outcome_json(o)).collect::<Vec<_>>(),
            "withFalse": outcomes.iter().filter(|o| !o.false_errors.is_empty())
                .map(outcome_json).collect::<Vec<_>>(),
        }));
    } else {
        println!(
            "{total} break(s) in {seconds:.1} s, {bad} with a false error ({:.2}%); \
             {still_parse} more still parsed and were skipped",
            rate((total, bad))
        );
        if unseen > 0 {
            println!(
                "{unseen} break(s) whose check reported no error at all: a fault of the tool's"
            );
        }
        for path in skipped {
            println!("skipped {path}");
        }
        println!("by recovery point:");
        for (point, row) in &by_point {
            println!(
                "  {point}: {} break(s), {} with a false error ({:.2}%)",
                row.0,
                row.1,
                rate(*row)
            );
        }
        if !by_code.is_empty() {
            println!("false errors by code (breaks giving one):");
            let mut codes: Vec<_> = by_code.iter().collect();
            codes.sort_by_key(|(_, n)| std::cmp::Reverse(**n));
            for (code, n) in codes {
                println!("  {code}: {n}");
            }
        }
        if !worst.is_empty() {
            println!("worst:");
            for o in worst {
                println!(
                    "  {}:{}: {} ({}): {} false error(s)",
                    o.path,
                    o.line,
                    o.how.word(),
                    o.point,
                    o.false_errors.len()
                );
                for e in &o.false_errors {
                    println!("    {} (line {}): {}", e.code, e.line, e.message);
                }
            }
        }
    }
    ExitCode::from(DONE)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn breaks_drop_each_lines_last_token_and_put_a_paren_mid_line() {
        let text = "namespace N\n\ndef f (n: Nat): Nat :=\n  n + 1\n";
        let broken: Vec<(u32, How, String)> = breaks(text)
            .into_iter()
            .map(|b| (b.line, b.how, b.edited))
            .collect();
        assert_eq!(
            broken,
            vec![
                (
                    3,
                    How::DropLast,
                    "namespace N\n\ndef f (n: Nat): Nat \n  n + 1\n".to_string()
                ),
                (
                    3,
                    How::StrayParen,
                    "namespace N\n\ndef f (n: ) Nat): Nat :=\n  n + 1\n".to_string()
                ),
                (
                    4,
                    How::DropLast,
                    "namespace N\n\ndef f (n: Nat): Nat :=\n  n + \n".to_string()
                ),
                (
                    4,
                    How::StrayParen,
                    "namespace N\n\ndef f (n: Nat): Nat :=\n  n ) + 1\n".to_string()
                ),
            ]
        );
    }

    #[test]
    fn rendered_errors_are_read_with_their_lines() {
        let report = "[E-PARSE] Error: expected a field name after `.`\n   ╭─[ a/b.sw:3:32 ]\n   │\n[E-TYPE-MISMATCH] Error: type mismatch\n   ╭─[ a/b.sw:4:15 ]\n[E-X] Error: elsewhere\n   ╭─[ a/c.sw:1:1 ]\n";
        let read = rendered_errors(report, "b.sw");
        assert_eq!(
            read.iter()
                .map(|r| (r.code.as_str(), r.line))
                .collect::<Vec<_>>(),
            vec![("E-PARSE", 3), ("E-TYPE-MISMATCH", 4)]
        );
    }
}
