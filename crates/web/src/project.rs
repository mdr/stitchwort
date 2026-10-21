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
    MAX_READS_PAST_END, OutputSink, failure, json_string, rendered, run_by_line_of, test_answer,
};

/// The project's name in messages: errors show `aoc/src/Aoc/Day02/Day02.sw`,
/// as the CLI does in the project's parent folder.
const PROJECT: &str = "aoc";

/// The tests run on threads with a big stack: the AoC proofs need more than
/// the 2 MiB a test thread has (in WebAssembly they fit its 128 KiB guard).
#[cfg(test)]
const TEST_STACK: usize = 256 * 1024 * 1024;

fn limits() -> stitchwort_core::Limits {
    #[cfg(test)]
    return stitchwort_core::Limits::for_stack(TEST_STACK);
    #[cfg(not(test))]
    super::session_limits()
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
/// shorter. Other files (`inputs/day01.txt`) are for `include`: see
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
    let mut session = Session::new();
    session.elab.limits = limits();
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

/// A file's path within the project, from its display name.
fn project_path(name: &str) -> &str {
    name.strip_prefix(PROJECT)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(name)
}

/// `"diagnostics": [...]`: one entry per diagnostic, with its severity, code
/// and the primary span's file (path within the project), line and column,
/// both counted from 1, the column in characters.
fn diagnostics_json(session: &Session, diagnostics: &[&Diagnostic]) -> String {
    let each: Vec<String> = diagnostics
        .iter()
        .map(|d| {
            let severity = match d.severity {
                Severity::Error => "error",
                Severity::Warning => "warning",
            };
            let place = d.primary_span().map(|span| {
                let file = session.sources.get(span.file);
                let before = &file.text[..(span.start as usize).min(file.text.len())];
                let line = before.matches('\n').count() + 1;
                let column = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
                format!(
                    r#","file":{},"line":{line},"column":{column}"#,
                    json_string(project_path(&file.name))
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
fn failed(session: &Session, diagnostics: Vec<Diagnostic>) -> String {
    let (warnings, errors): (Vec<_>, Vec<_>) = diagnostics
        .iter()
        .partition(|d| d.severity == Severity::Warning);
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
    let all: Vec<&Diagnostic> = errors.iter().chain(&warnings).copied().collect();
    let text: String = errors
        .iter()
        .map(|d| stitchwort_driver::render::render(&session.sources, d, false))
        .collect();
    format!(
        r#"{{"ok":false,"errors":{}{warnings_field},{}}}"#,
        json_string(&text),
        diagnostics_json(session, &all)
    )
}

/// Loads the project's files for `target`, or gives the answer for a load
/// that fails.
fn load(paths: &[String], texts: &[String], targets: &str) -> Result<Loaded, String> {
    let mut session = new_session(paths, texts);
    match session.load_project_sources(PROJECT, pairs(paths, texts), &target_of(targets)) {
        Ok(loaded) => Ok(Loaded {
            session,
            checked: loaded.checked,
        }),
        Err(diagnostics) => Err(failed(&session, diagnostics)),
    }
}

/// [`load`], shared by the read-only users (`check_project`, `test_project`
/// and `extract_project`), as `load_shared` is for single files.
fn load_shared(paths: &[String], texts: &[String], targets: &str) -> Result<Rc<Loaded>, String> {
    let key = (paths.to_vec(), texts.to_vec(), targets.to_string());
    LAST.with(|last| {
        let mut last = last.borrow_mut();
        if let Some((cached_key, cached)) = last.as_ref()
            && *cached_key == key
        {
            return cached.clone();
        }
        let loaded = load(paths, texts, targets).map(Rc::new);
        *last = Some((key, loaded.clone()));
        loaded
    })
}

/// The project's namespaces, from its files, parsing only: `{"ok": true,
/// "namespaces": [{"name": …, "files": [paths], "uses": [names]}]}`, or the
/// errors that stop that (a file with no namespace, a clash).
#[wasm_bindgen]
pub fn outline_project(paths: Vec<String>, texts: Vec<String>) -> String {
    let mut session = new_session(&paths, &texts);
    let analysis = analyse(&mut session, PROJECT, pairs(&paths, &texts));
    if !analysis.diagnostics.is_empty() {
        return failed(&session, analysis.diagnostics);
    }
    let each: Vec<String> = analysis
        .namespaces
        .iter()
        .map(|ns| {
            let files: Vec<String> = ns
                .files
                .iter()
                .map(|id| json_string(project_path(&session.sources.get(*id).name)))
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
pub fn check_project(paths: Vec<String>, texts: Vec<String>, targets: &str) -> String {
    match load_shared(&paths, &texts, targets) {
        Ok(loaded) => {
            let checked: Vec<String> = loaded.checked.iter().map(|n| json_string(n)).collect();
            let each: Vec<String> = loaded
                .session
                .warnings
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
                r#"{{"ok":true,"checked":[{}]{warnings},{}}}"#,
                checked.join(","),
                diagnostics_json(&loaded.session, &all)
            )
        }
        Err(failed) => failed,
    }
}

/// [`super::check_index`] for a project: the index of the namespaces in
/// `targets` (empty for the whole project) and what they use, with paths
/// within the project. Not cached.
#[wasm_bindgen]
pub fn check_index_project(paths: Vec<String>, texts: Vec<String>, targets: &str) -> String {
    let mut session = new_session(&paths, &texts);
    session.elab.enable_navigation();
    let ok = session
        .load_project_sources(PROJECT, pairs(&paths, &texts), &target_of(targets))
        .is_ok();
    stitchwort_driver::nav::index_json(&session, !ok, Some(ok), &format!("{PROJECT}/"))
}

/// [`super::test`] for a project: each result also has its `namespace`.
#[wasm_bindgen]
pub fn test_project(paths: Vec<String>, texts: Vec<String>, targets: &str, known: &str) -> String {
    match load_shared(&paths, &texts, targets) {
        Ok(loaded) => test_answer(&loaded.session, known, true),
        Err(failed) => failed,
    }
}

/// [`super::evaluate`] for a project: the expression is evaluated after
/// loading `targets`, with no namespace open, so it uses full names.
#[wasm_bindgen]
pub fn evaluate_project(
    paths: Vec<String>,
    texts: Vec<String>,
    targets: &str,
    expr: &str,
) -> String {
    let mut session = match load(&paths, &texts, targets) {
        Ok(loaded) => loaded.session,
        Err(failed) => return failed,
    };
    let result = session
        .parse_expression("expression", expr)
        .and_then(|e| session.elab.eval_expr(&e));
    match result {
        Ok((value, ty)) => format!(
            r#"{{"ok":true,"value":{},"type":{}}}"#,
            json_string(&value),
            json_string(&ty)
        ),
        Err(error) => failure(&rendered(&session, &[error])),
    }
}

/// [`super::extract`] for one namespace of a project, as `build --js NS`
/// does.
#[wasm_bindgen]
pub fn extract_project(paths: Vec<String>, texts: Vec<String>, namespace: &str) -> String {
    let loaded = match load_shared(&paths, &texts, namespace) {
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

/// [`super::run_streaming`] for a project: runs the function with the full
/// name `name` (as `stitchwort run NAME` does), after loading its namespace.
#[wasm_bindgen]
pub fn run_project_streaming(
    paths: Vec<String>,
    texts: Vec<String>,
    name: &str,
    input: &str,
    max_output: usize,
    sink: &OutputSink,
) -> String {
    let mut session = new_session(&paths, &texts);
    let analysis: Analysis = analyse(&mut session, PROJECT, pairs(&paths, &texts));
    if !analysis.diagnostics.is_empty() {
        return failed(&session, analysis.diagnostics);
    }
    let Some(namespace) = namespace_of(&analysis, name).map(str::to_string) else {
        let d = run_unknown_namespace(PROJECT, name, &analysis);
        return failed(&session, vec![d]);
    };
    if let Err(diagnostics) =
        session.load_analysis(PROJECT, analysis, &Target::Namespaces(vec![namespace]))
    {
        return failed(&session, diagnostics);
    }
    let main = match session.main_named(name, PROJECT) {
        Ok(main) => main,
        Err(error) => return failure(&rendered(&session, &[error])),
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

    /// The `.sw` files under `aoc/src` and the puzzle inputs under
    /// `aoc/inputs`, as (path within the project, text): the bundle.
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
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc/examples");
        std::fs::read_to_string(root.join(format!("day{day:02}.txt"))).expect("an example input")
    }

    /// What the page does for a day: its namespaces are `Aoc.DayNN` and
    /// `Aoc.DayNN.Proofs` if the outline has it.
    fn day_targets(outline: &str, day: u32) -> String {
        let program = format!("Aoc.Day{day:02}");
        let proofs = format!("{program}.Proofs");
        if outline.contains(&format!(r#""name":"{proofs}""#)) {
            format!("{program},{proofs}")
        } else {
            program
        }
    }

    /// The navigation index of a project: paths within it, a reference
    /// into another namespace, and a library target with its `std` marker.
    #[test]
    fn the_navigation_index_of_a_project() {
        big(|| {
            let paths = vec!["src/A/A.sw".to_string(), "src/B/B.sw".to_string()];
            let texts = vec![
                "namespace A\n\ndef two: Nat := 2\n".to_string(),
                "namespace B\n\nimport A (two)\n\ndef f (xs: List Nat): Nat := two + xs.length\n"
                    .to_string(),
            ];
            let index = check_index_project(paths, texts, "");
            assert!(
                index.starts_with(r#"{"version":1,"errors":false,"ok":true,"files":["#),
                "{index}"
            );
            assert!(index.contains(r#"{"path":"src/B/B.sw"}"#), "{index}");
            assert!(index.contains(r#""name":"A.two","kind":"def""#), "{index}");
            assert!(index.contains(r#""std":"core.sw""#), "{index}");
        });
    }

    #[test]
    fn every_aoc_day_checks_passes_its_tests_and_runs_on_its_example() {
        big(every_aoc_day_body);
    }

    fn every_aoc_day_body() {
        let (paths, texts) = aoc_files();
        let outline = outline_project(paths.clone(), texts.clone());
        assert!(
            outline.starts_with(r#"{"ok":true,"namespaces":["#),
            "{outline}"
        );
        assert!(
            outline.contains(
                r#"{"name":"Aoc.Day02","files":["src/Aoc/Day02/Day02.sw","src/Aoc/Day02/Input.sw"],"uses":["Aoc.Common"#
            ),
            "{outline}"
        );
        let whole = check_project(paths.clone(), texts.clone(), "");
        assert!(whole.starts_with(r#"{"ok":true,"checked":["#), "{whole}");
        for day in 1..=6 {
            let targets = day_targets(&outline, day);
            let checked = check_project(paths.clone(), texts.clone(), &targets);
            assert!(checked.starts_with(r#"{"ok":true"#), "day {day}: {checked}");
            let tests = test_project(paths.clone(), texts.clone(), &targets, "");
            assert!(tests.starts_with(r#"{"ok":true,"tests":["#), "day {day}");
            assert!(!tests.contains(r#""passed":false"#), "day {day}: {tests}");
            assert!(tests.contains(r#""namespace":"Aoc.Day"#), "day {day}");
            // `Input.sw` includes the real input from the bundle.
            assert!(tests.contains("real input"), "day {day}: {tests}");
            let main = format!("Aoc.Day{day:02}.main");
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
        let answer = check_project(paths, texts, "Aoc.Day02");
        assert!(
            answer.starts_with(r#"{"ok":false,"errors":"[E-"#),
            "{answer}"
        );
        assert!(answer.contains("[E-NAMESPACE-FAILED]"), "{answer}");
        assert!(
            answer.contains(r#""file":"src/Aoc/Common/Range.sw","line":"#),
            "{answer}"
        );
        assert!(answer.contains(r#""code":"E-NAMESPACE-FAILED","file":"src/Aoc/Day02/Day02.sw""#));
    }

    #[test]
    fn evaluates_with_full_names_and_extracts_a_namespace() {
        big(evaluate_body);
    }

    fn evaluate_body() {
        let (paths, texts) = aoc_files();
        let value = evaluate_project(
            paths.clone(),
            texts.clone(),
            "Aoc.Day02",
            "Aoc.Day02.solvePart1 Aoc.Day02.exampleRanges",
        );
        assert!(
            value.starts_with(r#"{"ok":true,"value":"1227775554""#),
            "{value}"
        );
        let nothing = extract_project(paths, texts, "Aoc.Day02");
        assert!(nothing.starts_with(r#"{"ok":true,"js":"#), "{nothing}");
    }
}
