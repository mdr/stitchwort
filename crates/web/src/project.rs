//! The playground's functions for projects of several files
//! (docs/proposals/playground-projects.md §2). Each takes the project's files
//! as two arrays of the same length, paths within the project and texts, and
//! a target, and goes through the same driver code as the CLI, so the answers
//! and the error text are the same.

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_driver::driver::Session;
use stitchwort_driver::project::{
    Analysis, MemoryFiles, Target, analyse, namespace_of, run_unknown_namespace,
};
use stitchwort_syntax::{Diagnostic, Severity};
use wasm_bindgen::prelude::wasm_bindgen;

use super::{
    MAX_READS_PAST_END, OutputSink, evaluate_in, failure, goals_field, json_string, rendered,
    run_by_line_of, split_goals, test_answer,
};

/// The tests run on threads with a big stack: the AoC proofs need more than
/// the 2 MiB a test thread has (in WebAssembly they fit its 256 KiB guard).
#[cfg(test)]
const TEST_STACK: usize = 256 * 1024 * 1024;

#[cfg(test)]
fn limits() -> stitchwort_core::Limits {
    stitchwort_core::Limits::for_stack(TEST_STACK)
}

/// A project loaded for a target: the session, and the namespaces checked.
struct Loaded {
    session: Session,
    checked: Vec<String>,
}

/// A load shared by the read-only calls, or the answer for one that failed.
type Shared = Result<Rc<Loaded>, String>;

/// What a load is keyed by: the files and the targets.
type Key = (Vec<String>, Vec<String>, String);

thread_local! {
    /// The most recent shared load, as for single files (`load_shared`).
    static LAST: RefCell<Option<(Key, Shared)>> =
        const { RefCell::new(None) };
}

/// The project's source files as (path, text) pairs. Unequal arrays use the
/// shorter. Other files (`inputs/2025/day01.txt`) are for `include`: see
/// [`new_session`].
fn pairs(paths: &[String], texts: &[String]) -> Vec<(String, String)> {
    paths
        .iter()
        .cloned()
        .zip(texts.iter().cloned())
        .filter(|(path, _)| path.ends_with(".sw"))
        .collect()
}

/// A session whose `include` reads the project's other files, those that
/// aren't `.sw` (the bundled puzzle inputs), from memory: the same files,
/// with the same paths, that the CLI reads from disk. No server is involved.
fn new_session(paths: &[String], texts: &[String]) -> Session {
    let mut session = super::new_session();
    #[cfg(test)]
    {
        session.elab.options.limits = limits();
    }
    let files = paths
        .iter()
        .cloned()
        .zip(texts.iter().cloned())
        .filter(|(path, _)| !path.ends_with(".sw"))
        .collect();
    session.include_from(Rc::new(MemoryFiles {
        files,
        reversed: false,
    }));
    session
}

fn target_of(targets: &str) -> Target {
    let names: Vec<String> = targets
        .split(',')
        .map(str::trim)
        .filter(|n| !n.is_empty())
        .map(str::to_string)
        .collect();
    if names.is_empty() {
        Target::Everything
    } else {
        Target::Namespaces(names)
    }
}

/// A file's path within the project, from its display name. Messages show
/// `aoc/src/Aoc/Year2025/Day02/Day02.sw`, as the CLI does in the project's parent
/// folder: the project's name (`project`, as the page gives it) and the path.
fn project_path<'a>(project: &str, name: &'a str) -> &'a str {
    name.strip_prefix(project)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(name)
}

/// `"diagnostics": [...]`: one entry per diagnostic, with its severity, code
/// and the primary span's file (path within the project), line and column,
/// both counted from 1, the column in characters. The span's end is
/// `endLine` and `endColumn` in the units of the navigation index's ranges
/// (the language server's): the line counted from 0, the column in UTF-16 code units
/// (what a JavaScript string and CodeMirror count).
fn diagnostics_json(project: &str, session: &Session, diagnostics: &[&Diagnostic]) -> String {
    let each: Vec<String> = diagnostics
        .iter()
        .map(|d| {
            let severity = match d.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
                Severity::Goal => "goal",
            };
            let place = d.primary_span().map(|span| {
                let file = session.sources.get(span.file);
                let before = &file.text[..(span.start as usize).min(file.text.len())];
                let line = before.matches('\n').count() + 1;
                let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
                let upto = &file.text[..(span.end as usize).clamp(before.len(), file.text.len())];
                let end_line = upto.matches('\n').count();
                let end_column = upto
                    .rsplit('\n')
                    .next()
                    .map_or(0, |l| l.encode_utf16().count());
                format!(
                    r#","file":{},"line":{line},"column":{column},"endLine":{end_line},"endColumn":{end_column}"#,
                    json_string(project_path(project, &file.name))
                )
            });
            format!(
                r#"{{"severity":"{severity}","code":{}{},"text":{}}}"#,
                json_string(d.code),
                place.unwrap_or_default(),
                json_string(&stitchwort_driver::render::render(
                    &session.sources,
                    d,
                    false
                ))
            )
        })
        .collect();
    format!(r#""diagnostics":[{}]"#, each.join(","))
}

/// `{"ok": false, "errors": "…", "warnings": […], "diagnostics": […]}` for
/// the diagnostics of a load that failed.
fn failed(project: &str, session: &Session, diagnostics: Vec<Diagnostic>) -> String {
    let (goals, others) = split_goals(diagnostics.clone());
    let (warnings, errors): (Vec<_>, Vec<_>) =
        others.iter().partition(|d| d.severity == Severity::Warning);
    let each: Vec<String> = warnings
        .iter()
        .map(|w| {
            json_string(&stitchwort_driver::render::render(
                &session.sources,
                w,
                false,
            ))
        })
        .collect();
    let warnings_field = if each.is_empty() {
        String::new()
    } else {
        format!(r#","warnings":[{}]"#, each.join(","))
    };
    let all: Vec<&Diagnostic> = errors
        .iter()
        .chain(&warnings)
        .copied()
        .chain(goals.iter())
        .collect();
    let text: String = errors
        .iter()
        .map(|d| stitchwort_driver::render::render(&session.sources, d, false))
        .collect();
    format!(
        r#"{{"ok":false,"errors":{}{warnings_field}{},{}}}"#,
        json_string(&text),
        goals_field(session, &goals),
        diagnostics_json(project, session, &all)
    )
}

/// Loads the project's files for `target`, or gives the answer for a load
/// that fails.
fn load(
    project: &str,
    paths: &[String],
    texts: &[String],
    targets: &str,
) -> Result<Loaded, String> {
    let mut session = new_session(paths, texts);
    match session.load_project_sources(project, pairs(paths, texts), &target_of(targets)) {
        Ok(loaded) => Ok(Loaded {
            session,
            checked: loaded.checked,
        }),
        Err(diagnostics) => Err(failed(project, &session, diagnostics)),
    }
}

/// [`load`], shared by the read-only users (`check_project`, `test_project`
/// and `extract_project`), as `load_shared` is for single files.
fn load_shared(
    project: &str,
    paths: &[String],
    texts: &[String],
    targets: &str,
) -> Result<Rc<Loaded>, String> {
    let key = (
        paths.to_vec(),
        texts.to_vec(),
        format!("{project}:{targets}"),
    );
    LAST.with(|last| {
        let mut last = last.borrow_mut();
        if let Some((cached_key, cached)) = last.as_ref()
            && *cached_key == key
        {
            return cached.clone();
        }
        let loaded = load(project, paths, texts, targets).map(Rc::new);
        *last = Some((key, loaded.clone()));
        loaded
    })
}

/// The project's namespaces, from its files, parsing only: `{"ok": true,
/// "namespaces": [{"name": …, "files": [paths], "uses": [names]}]}`, or the
/// errors that stop that (a file with no namespace, a clash).
#[wasm_bindgen]
pub fn outline_project(project: &str, paths: Vec<String>, texts: Vec<String>) -> String {
    let mut session = new_session(&paths, &texts);
    let analysis = analyse(&mut session, project, pairs(&paths, &texts));
    if !analysis.diagnostics.is_empty() {
        return failed(project, &session, analysis.diagnostics);
    }
    let each: Vec<String> = analysis
        .namespaces
        .iter()
        .map(|ns| {
            let files: Vec<String> = ns
                .files
                .iter()
                .map(|id| json_string(project_path(project, &session.sources.get(*id).name)))
                .collect();
            let mut uses: Vec<&str> = ns.edges.iter().map(|e| e.target.as_str()).collect();
            uses.sort();
            uses.dedup();
            let uses: Vec<String> = uses.into_iter().map(json_string).collect();
            format!(
                r#"{{"name":{},"files":[{}],"uses":[{}]}}"#,
                json_string(&ns.name),
                files.join(","),
                uses.join(",")
            )
        })
        .collect();
    format!(r#"{{"ok":true,"namespaces":[{}]}}"#, each.join(","))
}

/// Checks the namespaces in `targets` (comma-separated; empty for the whole
/// project) and what they use: `{"ok": true, "checked": [names],
/// "warnings"?, "diagnostics"}` or `{"ok": false, "errors", "warnings"?,
/// "diagnostics"}`.
#[wasm_bindgen]
pub fn check_project(
    project: &str,
    paths: Vec<String>,
    texts: Vec<String>,
    targets: &str,
) -> String {
    match load_shared(project, &paths, &texts, targets) {
        Ok(loaded) => {
            let checked: Vec<String> = loaded.checked.iter().map(|n| json_string(n)).collect();
            let (goals, warned) = split_goals(loaded.session.warnings.clone());
            let each: Vec<String> = warned
                .iter()
                .map(|w| {
                    json_string(&stitchwort_driver::render::render(
                        &loaded.session.sources,
                        w,
                        false,
                    ))
                })
                .collect();
            let warnings = if each.is_empty() {
                String::new()
            } else {
                format!(r#","warnings":[{}]"#, each.join(","))
            };
            let all: Vec<&Diagnostic> = loaded.session.warnings.iter().collect();
            format!(
                r#"{{"ok":true,"checked":[{}]{warnings}{},{}}}"#,
                checked.join(","),
                goals_field(&loaded.session, &goals),
                diagnostics_json(project, &loaded.session, &all)
            )
        }
        Err(failed) => failed,
    }
}

/// [`super::test`] for a project: each result also has its `namespace`.
#[wasm_bindgen]
pub fn test_project(
    project: &str,
    paths: Vec<String>,
    texts: Vec<String>,
    targets: &str,
    known: &str,
) -> String {
    match load_shared(project, &paths, &texts, targets) {
        Ok(loaded) => test_answer(&loaded.session, known, true),
        Err(failed) => failed,
    }
}

/// [`super::evaluate`] for a project: the expression is evaluated after
/// loading `targets`, with no namespace open, so it uses full names.
#[wasm_bindgen]
pub fn evaluate_project(
    project: &str,
    paths: Vec<String>,
    texts: Vec<String>,
    targets: &str,
    imports: &str,
    expr: &str,
) -> String {
    let mut session = match load(project, &paths, &texts, targets) {
        Ok(loaded) => loaded.session,
        Err(failed) => return failed,
    };
    evaluate_in(&mut session, imports, expr)
}

/// [`super::extract`] for one namespace of a project, as `build --js NS`
/// does.
#[wasm_bindgen]
pub fn extract_project(
    project: &str,
    paths: Vec<String>,
    texts: Vec<String>,
    namespace: &str,
) -> String {
    let loaded = match load_shared(project, &paths, &texts, namespace) {
        Ok(loaded) => loaded,
        Err(failed) => return failed,
    };
    match loaded.session.extract_namespace(namespace) {
        Ok(output) => format!(
            r#"{{"ok":true,"js":{},"dts":{}}}"#,
            json_string(&output.js),
            json_string(&output.dts)
        ),
        Err(error) => failure(&rendered(&loaded.session, &[error])),
    }
}

/// The project's session with the namespace of `name` loaded, and `name`'s
/// `main`; or the answer for a project that doesn't load.
fn load_main(
    project: &str,
    paths: &[String],
    texts: &[String],
    name: &str,
) -> Result<(Session, stitchwort_driver::run::Main), String> {
    let mut session = new_session(paths, texts);
    let analysis: Analysis = analyse(&mut session, project, pairs(paths, texts));
    if !analysis.diagnostics.is_empty() {
        return Err(failed(project, &session, analysis.diagnostics));
    }
    let Some(namespace) = namespace_of(&analysis, name).map(str::to_string) else {
        let d = run_unknown_namespace(project, name, &analysis);
        return Err(failed(project, &session, vec![d]));
    };
    if let Err(diagnostics) =
        session.load_analysis(project, analysis, &Target::Namespaces(vec![namespace]))
    {
        return Err(failed(project, &session, diagnostics));
    }
    match session.main_named(name, project) {
        Ok(main) => Ok((session, main)),
        Err(error) => Err(failure(&rendered(&session, &[error]))),
    }
}

/// [`super::live::start_live`] for a project: a live run of the function
/// with the full name `name`.
#[wasm_bindgen]
pub fn start_live_project(
    project: &str,
    paths: Vec<String>,
    texts: Vec<String>,
    name: &str,
) -> Result<super::live::LiveSession, String> {
    let (session, main) = load_main(project, &paths, &texts, name)?;
    super::live::live_from(session, main)
}

/// [`super::run_streaming`] for a project: runs the function with the full
/// name `name` (as `stitchwort run NAME` does), after loading its namespace.
#[wasm_bindgen]
pub fn run_project_streaming(
    project: &str,
    paths: Vec<String>,
    texts: Vec<String>,
    name: &str,
    input: &str,
    max_output: usize,
    sink: &OutputSink,
) -> String {
    let (session, main) = match load_main(project, &paths, &texts, name) {
        Ok(loaded) => loaded,
        Err(failure) => return failure,
    };
    let ran = run_by_line_of(
        session,
        Some(main),
        input,
        max_output,
        MAX_READS_PAST_END,
        &mut |text| sink.write(text),
    );
    match ran {
        Err(errors) => failure(&errors),
        Ok(Ok(())) => r#"{"ok":true,"ran":true}"#.into(),
        Ok(Err(errors)) => format!(
            r#"{{"ok":false,"errors":{},"ran":true}}"#,
            json_string(&errors)
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    const PROJECT: &str = "aoc";

    /// The `.sw` files under `aoc/src`, and the example and puzzle inputs
    /// under `aoc/examples` and `aoc/inputs` (by year), as (path within the project,
    /// text): the bundle, as `web/bundle-projects.sh` makes it.
    fn aoc_files() -> (Vec<String>, Vec<String>) {
        fn walk(dir: &Path, root: &Path, out: &mut Vec<(String, String)>) {
            let mut entries: Vec<_> = std::fs::read_dir(dir)
                .expect("a folder")
                .map(|e| e.expect("an entry").path())
                .collect();
            entries.sort();
            for path in entries {
                if path.is_dir() {
                    walk(&path, root, out);
                } else if path.extension().is_some_and(|e| e == "sw" || e == "txt") {
                    let relative = path.strip_prefix(root).expect("under the root");
                    out.push((
                        relative.to_string_lossy().into_owned(),
                        std::fs::read_to_string(&path).expect("readable"),
                    ));
                }
            }
        }
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
        let mut files = Vec::new();
        walk(&root.join("src"), &root, &mut files);
        walk(&root.join("examples"), &root, &mut files);
        walk(&root.join("inputs"), &root, &mut files);
        assert!(files.len() >= 10, "{} files", files.len());
        files.into_iter().unzip()
    }

    /// Runs `f` on a thread with the tests' big stack.
    fn big(f: fn()) {
        stitchwort_driver::driver::with_stack(TEST_STACK, f);
    }

    /// What each day prints for its example input, as the CLI does.
    const EXPECTED: [&str; 6] = [
        "Part 1: 3\nPart 2: 6\n",
        "Part 1: 1227775554\nPart 2: 4174379265\n",
        "Part 1: 357\nPart 2: 3121910778619\n",
        "Part 1: 13\nPart 2: 43\n",
        "Part 1: 3\nPart 2: 14\n",
        "Part 1: 4277556\nPart 2: 3263827\n",
    ];

    fn example(day: u32) -> String {
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc/examples/2025");
        std::fs::read_to_string(root.join(format!("day{day:02}.txt"))).expect("an example input")
    }

    /// What the page does for a day of 2025: its namespaces are `Aoc.Year2025.DayNN`, with
    /// `.Tests` and `.Proofs` under it if the outline has them.
    fn day_targets(outline: &str, day: u32) -> String {
        let program = format!("Aoc.Year2025.Day{day:02}");
        let mut targets = vec![program.clone()];
        for extra in ["Tests", "Proofs"] {
            let name = format!("{program}.{extra}");
            if outline.contains(&format!(r#""name":"{name}""#)) {
                targets.push(name);
            }
        }
        targets.join(",")
    }

    #[test]
    fn every_aoc_day_checks_passes_its_tests_and_runs_on_its_example() {
        big(every_aoc_day_body);
    }

    /// Checks the library once and has every later session in this thread
    /// replay it, as the page does from `std.cache` (`load_library_cache`).
    /// Without it each of the test's sessions would check the library from
    /// source, about 10 s each.
    fn replay_the_library_from_one_check() {
        use stitchwort_driver::check_cache::BundleRecorder;
        let mut session = new_session(&[], &[]);
        let recorder = std::rc::Rc::new(BundleRecorder::default());
        session.elab.set_check_cache(recorder.clone());
        let left_out = session.elab.load_libraries_that_check();
        let bundle = std::sync::Arc::new(recorder.finish(left_out));
        let set = super::super::SHARED.with(|options| options.library.set(bundle).is_ok());
        assert!(set, "the library was already cached");
    }

    fn every_aoc_day_body() {
        replay_the_library_from_one_check();
        let (paths, texts) = aoc_files();
        let outline = outline_project(PROJECT, paths.clone(), texts.clone());
        assert!(
            outline.starts_with(r#"{"ok":true,"namespaces":["#),
            "{outline}"
        );
        assert!(
            outline.contains(
                r#"{"name":"Aoc.Year2025.Day02","files":["src/Aoc/Year2025/Day02/Day02.sw"],"uses":["Aoc.Common"#
            ),
            "{outline}"
        );
        let whole = check_project(PROJECT, paths.clone(), texts.clone(), "");
        assert!(whole.starts_with(r#"{"ok":true,"checked":["#), "{whole}");
        for day in 1..=6 {
            let targets = day_targets(&outline, day);
            let checked = check_project(PROJECT, paths.clone(), texts.clone(), &targets);
            assert!(checked.starts_with(r#"{"ok":true"#), "day {day}: {checked}");
            let tests = test_project(PROJECT, paths.clone(), texts.clone(), &targets, "");
            assert!(tests.starts_with(r#"{"ok":true,"tests":["#), "day {day}");
            assert!(!tests.contains(r#""passed":false"#), "day {day}: {tests}");
            assert!(
                tests.contains(r#""namespace":"Aoc.Year2025.Day"#),
                "day {day}"
            );
            // `Tests/Input.sw` includes the real input from the bundle.
            assert!(tests.contains("real input"), "day {day}: {tests}");
            let main = format!("Aoc.Year2025.Day{day:02}.main");
            let mut out = String::new();
            let answer =
                run_project_streaming_for_test(&paths, &texts, &main, &example(day), &mut out);
            assert_eq!(answer, r#"{"ok":true,"ran":true}"#, "day {day}: {out}");
            assert_eq!(out, EXPECTED[day as usize - 1], "day {day}");
        }
    }

    /// [`run_project_streaming`] needs a JavaScript sink, so tests go through
    /// the same pieces with a Rust one.
    fn run_project_streaming_for_test(
        paths: &[String],
        texts: &[String],
        name: &str,
        input: &str,
        out: &mut String,
    ) -> String {
        let mut session = new_session(paths, texts);
        let analysis = analyse(&mut session, PROJECT, pairs(paths, texts));
        let namespace = namespace_of(&analysis, name)
            .expect("a namespace")
            .to_string();
        session
            .load_analysis(PROJECT, analysis, &Target::Namespaces(vec![namespace]))
            .unwrap_or_else(|_| panic!("loads"));
        let main = session.main_named(name, PROJECT).expect("a main");
        let ran = run_by_line_of(session, Some(main), input, 100_000, 100, &mut |t| {
            out.push_str(t)
        });
        match ran {
            Ok(Ok(())) => r#"{"ok":true,"ran":true}"#.into(),
            other => format!("{other:?}"),
        }
    }

    #[test]
    fn an_error_in_a_shared_file_comes_with_its_file_and_line() {
        big(shared_file_error_body);
    }

    fn shared_file_error_body() {
        let (paths, mut texts) = aoc_files();
        let at = paths
            .iter()
            .position(|p| p == "src/Aoc/Common/Range.sw")
            .expect("the shared file");
        texts[at].push_str("\ndef broken : Nat := rfl\n");
        let answer = check_project(PROJECT, paths, texts, "Aoc.Year2025.Day02");
        assert!(
            answer.starts_with(r#"{"ok":false,"errors":"[E-"#),
            "{answer}"
        );
        // Day 2 doesn't use `broken`, so it's checked as usual (D3524).
        assert!(!answer.contains("[E-USES-FAILED]"), "{answer}");
        assert!(
            answer.contains(r#""file":"src/Aoc/Common/Range.sw","line":"#),
            "{answer}"
        );
        // The `rfl` at the end of `def broken : Nat := rfl`, line 28 counted
        // from 1: the end is line 27 counted from 0, after the 23rd unit.
        assert!(
            answer.contains(r#""line":28,"column":21,"endLine":27,"endColumn":23,"#),
            "{answer}"
        );
    }

    #[test]
    fn evaluates_with_full_names_and_extracts_a_namespace() {
        big(evaluate_body);
    }

    fn evaluate_body() {
        let (paths, texts) = aoc_files();
        let value = evaluate_project(
            PROJECT,
            paths.clone(),
            texts.clone(),
            "Aoc.Year2025.Day02,Aoc.Year2025.Day02.Tests",
            "",
            "Aoc.Year2025.Day02.Tests.exampleRanges.map Aoc.Year2025.Day02.solvePart1",
        );
        assert!(
            value.starts_with(r#"{"ok":true,"value":"Ok 1227775554""#),
            "{value}"
        );
        // An import of the project's namespaces gives short names.
        let short = evaluate_project(
            PROJECT,
            paths.clone(),
            texts.clone(),
            "Aoc.Year2025.Day02,Aoc.Year2025.Day02.Tests",
            "import Aoc.Year2025.Day02 (solvePart1)\nimport Aoc.Year2025.Day02.Tests (exampleRanges)",
            "exampleRanges.map solvePart1",
        );
        assert!(
            short.starts_with(r#"{"ok":true,"value":"Ok 1227775554""#),
            "{short}"
        );
        let nothing = extract_project(PROJECT, paths, texts, "Aoc.Year2025.Day02");
        assert!(nothing.starts_with(r#"{"ok":true,"js":"#), "{nothing}");
    }
}
