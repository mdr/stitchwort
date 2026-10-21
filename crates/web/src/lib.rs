//! The browser playground's interface to the compiler. Each function takes the
//! editor's source text and returns a JSON string, so the page needs no
//! knowledge of the compiler's types.
//!
//! [`check`]'s answer, and any function's answer when the source doesn't
//! load, also has the program's warnings, each rendered as text:
//! `"warnings": ["…", …]`, left out when there are none. (The page checks
//! before anything else, so it gets them from there.)

mod project;

use std::cell::RefCell;
use std::io::{self, BufRead, Read, Write};
use std::rc::Rc;

use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_driver::render::render;
use stitchwort_driver::run::{Main, RunError};
use stitchwort_syntax::{Diagnostic, Severity};
use wasm_bindgen::prelude::wasm_bindgen;

/// The file name shown in error messages.
const FILE: &str = "playground.sw";

/// The stack this build runs on, set by `build.rs`: the resource limits are
/// sized to it.
fn stack() -> usize {
    env!("STITCHWORT_STACK")
        .parse()
        .expect("build.rs sets a number")
}

/// The limits sessions run with: sized to the stack, except that in
/// WebAssembly the stack guard is much smaller (see `build.rs`).
fn session_limits() -> stitchwort_core::Limits {
    let mut l = stitchwort_core::Limits::for_stack(stack());
    if let Ok(guard) = env!("STITCHWORT_GUARD").parse() {
        l.stack = guard;
    }
    l
}

/// The resource limits programs run with:
/// `{"stack": …, "frames": …, "work": …, "size": …}`.
#[wasm_bindgen]
pub fn limits() -> String {
    let l = session_limits();
    format!(
        r#"{{"stack":{},"guarded":{},"frames":{},"work":{},"size":{}}}"#,
        stack(),
        l.stack,
        l.frames,
        l.work,
        l.size
    )
}

/// Checks a program: `{"ok": true}` or `{"ok": false, "errors": "…"}`, with
/// its warnings, if any.
#[wasm_bindgen]
pub fn check(source: &str) -> String {
    match load_shared(source) {
        Ok(session) => format!(
            r#"{{"ok":true{}}}"#,
            warnings_field(&session, &session.warnings)
        ),
        Err(failed) => failed,
    }
}

/// The code navigation index of a program (docs/proposals/code-navigation.md):
/// the version 1 JSON the CLI's `check --index` writes, with `"ok"` added.
/// Written whether or not the program checks, for the parts that were
/// elaborated. Not cached: it loads the program again with recording on.
#[wasm_bindgen]
pub fn check_index(source: &str) -> String {
    let mut session = Session::new();
    session.elab.limits = session_limits();
    session.elab.enable_navigation();
    let ok = session.load(FILE, source).is_ok();
    stitchwort_driver::nav::index_json(&session, !ok, Some(ok), "")
}

/// The text of an embedded library file, by the `std` value of a file of
/// the index (`List/Toolkit.sw`; `core.sw` is the core): empty if there's
/// none.
#[wasm_bindgen]
pub fn std_source(path: &str) -> String {
    stitchwort_driver::nav::std_source(path, session_limits().stack).unwrap_or_default()
}

/// Runs a program's tests, reusing the results in `known`:
/// `{"ok": true, "tests": [{"name": …, "passed": …, "outcome": …, "cached": …}],
/// "added": "…"}`, where the outcome is `passed`, `failed`, or what the test
/// ran out of. `known` is one `KEY passed` or `KEY failed` per line, and
/// malformed lines are ignored; `added` is the results that weren't cached,
/// in the same format (empty if none).
#[wasm_bindgen]
pub fn test(source: &str, known: &str) -> String {
    let session = match load_shared(source) {
        Ok(session) => session,
        Err(failed) => return failed,
    };
    test_answer(&session, known, false)
}

/// [`test`]'s answer for a loaded session; each result also has its
/// `namespace` if `with_namespace`.
fn test_answer(session: &Session, known: &str, with_namespace: bool) -> String {
    let cache = Cache::memory(known_results(known));
    let tests: Vec<String> = session
        .run_tests(&cache)
        .iter()
        .map(|r| {
            let outcome = match r.outcome {
                Outcome::Passed => "passed".to_string(),
                Outcome::Failed => "failed".to_string(),
                Outcome::OutOfResources(e) => format!("no result: {e}"),
            };
            let namespace = if with_namespace {
                format!(r#","namespace":{}"#, json_string(&r.namespace))
            } else {
                String::new()
            };
            format!(
                r#"{{"name":{}{namespace},"passed":{},"outcome":{},"cached":{}}}"#,
                json_string(&r.name),
                r.outcome == Outcome::Passed,
                json_string(&outcome),
                r.cached
            )
        })
        .collect();
    let added: String = cache
        .added()
        .iter()
        .map(|(key, outcome)| {
            let outcome = match outcome {
                Outcome::Passed => "passed",
                Outcome::Failed => "failed",
                Outcome::OutOfResources(_) => return String::new(),
            };
            format!("{key} {outcome}\n")
        })
        .collect();
    format!(
        r#"{{"ok":true,"tests":[{}],"added":{}}}"#,
        tests.join(","),
        json_string(&added)
    )
}

/// The cached results in `known`, one `KEY passed` or `KEY failed` per line.
fn known_results(known: &str) -> impl Iterator<Item = (String, Outcome)> + '_ {
    known.lines().filter_map(|line| {
        let (key, outcome) = line.rsplit_once(' ')?;
        let outcome = match outcome {
            "passed" => Outcome::Passed,
            "failed" => Outcome::Failed,
            _ => return None,
        };
        Some((key.to_string(), outcome))
    })
}

/// Evaluates an expression in the context of a program:
/// `{"ok": true, "value": "…", "type": "…"}`.
#[wasm_bindgen]
pub fn evaluate(source: &str, expr: &str) -> String {
    let mut session = match load(source) {
        Ok(session) => session,
        Err(failed) => return failed,
    };
    let result = session
        .parse_expression("expression", expr)
        .and_then(|e| session.elab.eval_expr(&e));
    match result {
        Ok((value, ty)) => {
            format!(
                r#"{{"ok":true,"value":{},"type":{}}}"#,
                json_string(&value),
                json_string(&ty)
            )
        }
        Err(error) => failure_in(&session, &[error]),
    }
}

/// Extracts a program's exports: `{"ok": true, "js": "…", "dts": "…"}`.
#[wasm_bindgen]
pub fn extract(source: &str) -> String {
    let session = match load_shared(source) {
        Ok(session) => session,
        Err(failed) => return failed,
    };
    match session.extract() {
        Ok(output) => format!(
            r#"{{"ok":true,"js":{},"dts":{}}}"#,
            json_string(&output.js),
            json_string(&output.dts)
        ),
        Err(error) => failure_in(&session, &[error]),
    }
}

/// How many times a run may ask for a line after its input has run out
/// (`readLine` giving `Nothing`). Printing is bounded by the output cap, and
/// reading lines by the input, so this bounds how many operations a run
/// performs: a program that keeps reading at the end of its input stops at
/// once with `E-INPUT`, rather than when the page's timeout stops it.
pub const MAX_READS_PAST_END: usize = 10_000;

/// Runs a program's `main`, as `stitchwort run` does, with `input` as its
/// input: `readLine` gives its lines, then `Nothing`. Returns `{"ok": true,
/// "output": "…"}`, or `{"ok": false, "errors": "…", "output": "…"}` with
/// what was printed before the error. Each step between operations has the
/// same resource limits as a test, and the program is stopped with
/// `E-OUTPUT` once it tries to print more than `max_output` bytes, or with
/// `E-INPUT` once it has read past the end of its input more than
/// [`MAX_READS_PAST_END`] times.
#[wasm_bindgen]
pub fn run(source: &str, input: &str, max_output: usize) -> String {
    let session = match load(source) {
        Ok(session) => session,
        Err(failed) => return failed,
    };
    run_loaded(session, input, max_output, MAX_READS_PAST_END)
}

/// [`run`], in a session that's already loaded.
fn run_loaded(session: Session, input: &str, max_output: usize, max_past_end: usize) -> String {
    let mut bytes = Vec::new();
    let ran = run_in(session, input, max_output, max_past_end, &mut |b| {
        bytes.extend_from_slice(b)
    });
    // The cap can cut a character in two.
    let printed = json_string(&String::from_utf8_lossy(&bytes));
    match ran {
        Err(errors) => failure(&errors),
        Ok(Ok(())) => format!(r#"{{"ok":true,"output":{printed}}}"#),
        Ok(Err(errors)) => format!(
            r#"{{"ok":false,"errors":{},"output":{printed}}}"#,
            json_string(&errors)
        ),
    }
}

#[wasm_bindgen]
extern "C" {
    /// Where [`run_streaming`] sends a program's output as it's printed: a
    /// JavaScript object with a `write(text)` method.
    pub type OutputSink;

    #[wasm_bindgen(method)]
    fn write(this: &OutputSink, text: &str);
}

/// [`run`], but sending the output to `sink` as it's printed, a `print` at a
/// time, so that a run that's stopped still shows what it printed. Returns
/// `{"ok": true, "ran": true}`, `{"ok": false, "errors": "…", "ran": true}`
/// for an error once `main` had started, or `{"ok": false, "errors": "…"}`.
#[wasm_bindgen]
pub fn run_streaming(source: &str, input: &str, max_output: usize, sink: &OutputSink) -> String {
    let session = match load(source) {
        Ok(session) => session,
        Err(failed) => return failed,
    };
    let ran = run_by_line(
        session,
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

/// [`run_in`], passing on the output a line at a time. Each `print` writes
/// its text, then a line ending, so each line is one `print`. A write is only
/// cut short at the cap; then the last piece ends with U+FFFD if the cut went
/// through a character, as in [`run`].
fn run_by_line(
    session: Session,
    input: &str,
    max_output: usize,
    max_past_end: usize,
    print: &mut dyn FnMut(&str),
) -> Ran {
    run_by_line_of(session, None, input, max_output, max_past_end, print)
}

/// [`run_by_line`] for `main` if given, else the loaded program's own.
fn run_by_line_of(
    session: Session,
    main: Option<Main>,
    input: &str,
    max_output: usize,
    max_past_end: usize,
    print: &mut dyn FnMut(&str),
) -> Ran {
    let mut line = Vec::new();
    let mut by_line = |b: &[u8]| {
        line.extend_from_slice(b);
        if b.ends_with(b"\n") {
            print(&String::from_utf8_lossy(&line));
            line.clear();
        }
    };
    let ran = match main {
        None => run_in(session, input, max_output, max_past_end, &mut by_line),
        Some(main) => run_main_in(
            session,
            &main,
            input,
            max_output,
            max_past_end,
            &mut by_line,
        ),
    };
    if !line.is_empty() {
        print(&String::from_utf8_lossy(&line));
    }
    ran
}

/// How a run went: `Err` with the rendered errors if `main` couldn't start,
/// otherwise `Ok` with the errors it stopped with, if any.
type Ran = Result<Result<(), String>, String>;

/// Runs `main` in a session that's already loaded, passing what it prints to
/// `print` as it's written.
fn run_in(
    mut session: Session,
    input: &str,
    max_output: usize,
    max_past_end: usize,
    print: &mut dyn FnMut(&[u8]),
) -> Ran {
    let main = match session.main() {
        Ok(main) => main,
        Err(error) => return Err(rendered(&session, &[error])),
    };
    run_main_in(session, &main, input, max_output, max_past_end, print)
}

/// [`run_in`] for a `main` that's already found.
fn run_main_in(
    session: Session,
    main: &Main,
    input: &str,
    max_output: usize,
    max_past_end: usize,
    print: &mut dyn FnMut(&[u8]),
) -> Ran {
    let mut output = Capped {
        print,
        written: 0,
        max: max_output,
        full: false,
    };
    let mut input = Scripted {
        rest: input.as_bytes(),
        mid_line: false,
        past_end: 0,
        max_past_end,
    };
    let result = session.run_main(main, &mut input, &mut output);
    Ok(result.map_err(|error| {
        let error = match error {
            RunError::Write(_) if output.full => Diagnostic::error(
                "E-OUTPUT",
                format!("the program printed more than {max_output} bytes, the playground's limit"),
            )
            .with_label(main.span, "while running this program"),
            RunError::Read(_) if input.past_end > max_past_end => Diagnostic::error(
                "E-INPUT",
                format!(
                    "the program read past the end of its input more than {max_past_end} times, \
                     the playground's limit"
                ),
            )
            .with_label(main.span, "while running this program")
            .with_note("`IO.readLine()` gives `Nothing` at the end of the input"),
            error => error.diagnostic(main),
        };
        rendered(&session, &[error])
    }))
}

/// Output that passes on at most `max` bytes, and fails once more is
/// written.
struct Capped<'a> {
    print: &'a mut dyn FnMut(&[u8]),
    written: usize,
    max: usize,
    full: bool,
}

impl Write for Capped<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let room = self.max - self.written;
        if room == 0 && !buf.is_empty() {
            self.full = true;
            return Err(io::Error::other("the output budget is used up"));
        }
        let n = room.min(buf.len());
        (self.print)(&buf[..n]);
        self.written += n;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The input box's text, which fails once it has been read past its end
/// more than `max_past_end` times.
struct Scripted<'a> {
    rest: &'a [u8],
    /// Part of a last line without a line ending has been read, so the next
    /// look at the empty rest ends that line, rather than reading past the
    /// end.
    mid_line: bool,
    past_end: usize,
    max_past_end: usize,
}

impl Read for Scripted<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.fill_buf()?.read(buf)?;
        self.consume(n);
        Ok(n)
    }
}

impl BufRead for Scripted<'_> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.rest.is_empty() {
            if self.mid_line {
                self.mid_line = false;
            } else {
                self.past_end += 1;
                if self.past_end > self.max_past_end {
                    return Err(io::Error::other("read past the end too often"));
                }
            }
        }
        Ok(self.rest)
    }

    fn consume(&mut self, n: usize) {
        self.mid_line = n > 0 && self.rest[n - 1] != b'\n';
        self.rest = &self.rest[n..];
    }
}

/// A session, or the answer for a source that doesn't load.
type Loaded = Result<Rc<Session>, String>;

// The module is single-threaded in a Web Worker, so the most recent load is
// kept per thread rather than behind a lock.
thread_local! {
    /// The most recent [`load`] result, with the source text it came from.
    static LAST_LOAD: RefCell<Option<(String, Loaded)>> = const { RefCell::new(None) };
    /// How many times [`load`] has run, for tests.
    #[cfg(test)]
    static LOADS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A shared session with `source` loaded, or the answer for a source that
/// doesn't load: its errors, and its warnings, if any.
///
/// The page asks `check` and then `test` (or `extract`) for exactly the same
/// source when it opens or edits a program. A source checks the same way every
/// time, so the session from the first check can serve the rest. Only the
/// read-only users (`check`, `test` and `extract`) share it; `evaluate`, `run`
/// and `run_streaming` need a session of their own and call [`load`] directly.
fn load_shared(source: &str) -> Result<Rc<Session>, String> {
    LAST_LOAD.with(|last| {
        let mut last = last.borrow_mut();
        if let Some((cached_source, cached)) = last.as_ref()
            && cached_source.as_str() == source
        {
            return cached.clone();
        }
        let loaded = load(source).map(Rc::new);
        *last = Some((source.to_string(), loaded.clone()));
        loaded
    })
}

/// A session with `source` loaded, or the answer for a source that doesn't
/// load: its errors, and its warnings, if any.
fn load(source: &str) -> Result<Session, String> {
    #[cfg(test)]
    LOADS.with(|loads| loads.set(loads.get() + 1));
    let mut session = Session::new();
    session.elab.limits = session_limits();
    match session.load(FILE, source) {
        Ok(_) => Ok(session),
        Err(diagnostics) => {
            let (warnings, errors): (Vec<_>, Vec<_>) = diagnostics
                .into_iter()
                .partition(|d| d.severity == Severity::Warning);
            Err(format!(
                r#"{{"ok":false,"errors":{}{}}}"#,
                json_string(&rendered(&session, &errors)),
                warnings_field(&session, &warnings)
            ))
        }
    }
}

/// `,"warnings":["…",…]`, or nothing if there are none.
fn warnings_field(session: &Session, warnings: &[Diagnostic]) -> String {
    if warnings.is_empty() {
        return String::new();
    }
    let each: Vec<String> = warnings
        .iter()
        .map(|w| json_string(&render(&session.sources, w, false)))
        .collect();
    format!(r#","warnings":[{}]"#, each.join(","))
}

fn rendered(session: &Session, errors: &[Diagnostic]) -> String {
    errors
        .iter()
        .map(|d| render(&session.sources, d, false))
        .collect()
}

fn failure(errors: &str) -> String {
    format!(r#"{{"ok":false,"errors":{}}}"#, json_string(errors))
}

fn failure_in(session: &Session, errors: &[Diagnostic]) -> String {
    failure(&rendered(session, errors))
}

fn json_string(text: &str) -> String {
    let mut out = String::from('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexes_a_program_for_navigation_and_serves_library_text() {
        let index = check_index("def f (xs: List Nat): Nat := xs.length\n");
        assert!(
            index.starts_with(r#"{"version":1,"errors":false,"ok":true,"files":["#),
            "{index}"
        );
        assert!(index.contains(r#"{"path":"playground.sw"}"#), "{index}");
        assert!(index.contains(r#""name":"Std.List.length""#), "{index}");
        let failed = check_index("def f : Nat := rfl\n");
        assert!(failed.contains(r#""errors":true,"ok":false"#), "{failed}");
        assert!(std_source("core.sw").contains("type List"));
        assert_eq!(std_source("nope.sw"), "");
    }

    #[test]
    fn reports_success_errors_tests_values_and_extracted_code() {
        assert_eq!(check("def x : Nat := 1\n"), r#"{"ok":true}"#);
        let errors = check("def x : Nat := rfl\n");
        assert!(
            errors.starts_with(r#"{"ok":false,"errors":"[E-TYPE-MISMATCH]"#),
            "{errors}"
        );
        let tests = test("test \"one\" := True\ntest \"two\" := False\n", "");
        assert!(
            tests.starts_with(
                r#"{"ok":true,"tests":[{"name":"one","passed":true,"outcome":"passed","cached":false},{"name":"two","passed":false,"outcome":"failed","cached":false}],"added":""#
            ),
            "{tests}"
        );
        assert!(tests.ends_with(r#""}"#), "{tests}");
        assert_eq!(
            evaluate("def double (n : Nat) : Nat := n + n\n", "double 4"),
            r#"{"ok":true,"value":"8","type":"Nat"}"#
        );
        let js = extract("export def f (n : Nat) : Nat := n\n");
        assert!(js.contains(r#""js":"// Generated by stitchwort"#), "{js}");
    }

    /// Forgets the remembered load and resets the [`load`] count.
    fn reset_loads() {
        LAST_LOAD.with(|last| *last.borrow_mut() = None);
        LOADS.with(|loads| loads.set(0));
    }

    /// How many times [`load`] has run on this thread.
    fn loads() -> usize {
        LOADS.with(std::cell::Cell::get)
    }

    #[test]
    fn check_then_test_answers_as_fresh_loads_do() {
        let passing = "test \"one\" := True\ntest \"two\" := False\n";
        let failing = "def x : Nat := rfl\n";
        for source in [passing, failing] {
            reset_loads();
            let fresh_test = test(source, "");
            reset_loads();
            let fresh_check = check(source);
            reset_loads();
            let shared_check = check(source);
            let shared_test = test(source, "");
            assert_eq!(shared_check, fresh_check, "{source}");
            assert_eq!(shared_test, fresh_test, "{source}");
        }
    }

    #[test]
    fn a_second_source_replaces_the_remembered_one() {
        reset_loads();
        assert_eq!(check("def a : Nat := 1\n"), r#"{"ok":true}"#);
        let errors = check("def b : Nat := rfl\n");
        assert!(
            errors.starts_with(r#"{"ok":false,"errors":"[E-TYPE-MISMATCH]"#),
            "{errors}"
        );
        assert!(!errors.contains("def a"), "{errors}");
        assert_eq!(loads(), 2);
    }

    #[test]
    fn read_only_calls_share_a_load() {
        let source = "test \"one\" := True\n";
        reset_loads();
        check(source);
        test(source, "");
        extract(source);
        assert_eq!(loads(), 1);

        reset_loads();
        check(source);
        check("def x : Nat := 1\n");
        assert_eq!(loads(), 2);

        reset_loads();
        evaluate(source, "1");
        evaluate(source, "1");
        assert_eq!(loads(), 2);
    }

    #[test]
    fn reuses_known_test_results_and_reports_new_ones() {
        let source = "test \"one\" := True\ntest \"two\" := False\n";
        let first = test(source, "");
        assert!(!first.contains(r#""cached":true"#), "{first}");
        let start = first.find(r#""added":""#).expect("added") + r#""added":""#.len();
        let end = start + first[start..].find('"').expect("the string ends");
        let added = first[start..end].replace(r#"\n"#, "\n");
        assert_eq!(added.lines().count(), 2, "{added}");
        assert!(
            added
                .lines()
                .all(|line| line.ends_with(" passed") || line.ends_with(" failed")),
            "{added}"
        );
        let second = test(source, &added);
        assert!(!second.contains(r#""cached":false"#), "{second}");
        assert!(second.contains(r#""added":"""#), "{second}");
        // Malformed lines are ignored.
        let third = test(source, &format!("nonsense\n{added}"));
        assert!(!third.contains(r#""cached":false"#), "{third}");
    }

    #[test]
    fn reports_warnings_apart_from_errors() {
        let warned = "def size : List a -> Nat\n  \
                      | Nil => 0\n  \
                      | Cons _ xs => Succ (size xs)\n\n\
                      def a : Type := Nat\n";
        let checked = check(warned);
        assert!(
            checked.starts_with(r#"{"ok":true,"warnings":["[W-MODULE-NAME] Warning:"#),
            "{checked}"
        );
        assert_eq!(checked.matches("[W-MODULE-NAME]").count(), 1, "{checked}");
        // With an error too, each is in its own field.
        let failed = check(&format!("{warned}def bad : Nat := rfl\n"));
        let (errors, warnings) = failed.split_once(r#","warnings":"#).expect("warnings");
        assert!(
            errors.starts_with(r#"{"ok":false,"errors":"[E-TYPE-MISMATCH]"#),
            "{failed}"
        );
        assert!(!errors.contains("W-MODULE-NAME"), "{failed}");
        assert!(
            warnings.starts_with(r#"["[W-MODULE-NAME] Warning:"#),
            "{failed}"
        );
        // Other answers have them when the source doesn't load.
        assert!(test(&format!("{warned}def bad : Nat := rfl\n"), "").contains("[W-MODULE-NAME]"));
    }

    /// The `"output"` field of a result from [`run`].
    fn printed(result: &str) -> &str {
        let start = result.find(r#""output":""#).expect("it has output") + 10;
        &result[start..result.len() - 2]
    }

    #[test]
    fn runs_main_with_scripted_input() {
        let adder = include_str!("../../../examples/accept/adder.sw");
        assert_eq!(
            run(adder, "Ada\n40\ntwo\n2\n", 100_000),
            r#"{"ok":true,"output":"What's your name?\nHello, Ada! Type numbers to add, one per line, and an empty line to stop.\n  total: 40\n\"two\" isn't a number; skipped\n  total: 42\nThe sum is 42. Goodbye, Ada.\n"}"#
        );
        // No input at all: `readLine` gives `Nothing`.
        assert!(
            run(adder, "", 100_000).contains(r"Hello, stranger!"),
            "{}",
            run(adder, "", 100_000)
        );
        // An empty line is `Just ""`, and stops adding; a final line without
        // a line ending is still a line.
        let echo = "def textOr (d : Text) : Maybe Text -> Text\n  \
                    | Nothing => d\n  \
                    | Just t  => t\n\n\
                    def main () : {IO} () :=\n  \
                    IO.print (textOr \"none\" (IO.readLine ()))\n  \
                    IO.print (textOr \"none\" (IO.readLine ()))\n  \
                    IO.print (textOr \"none\" (IO.readLine ()))\n";
        assert_eq!(printed(&run(echo, "\nlast", 1000)), r"\nlast\nnone\n");
        // `readAll` gives the rest of the input as it is, then "".
        let rest = "def main () : {IO} () :=\n  \
                    IO.print (Nat.toText (List.length (IO.readAllLines ())))\n  \
                    IO.print (IO.readAll ())\n";
        assert_eq!(printed(&run(rest, "a\r\nb", 1000)), r"2\n\n");
        let all = "def main () : {IO} () :=\n  IO.print (IO.readAll ())\n";
        assert_eq!(printed(&run(all, "a\r\nb", 1000)), r"a\r\nb\n");
        assert_eq!(printed(&run(all, "", 1000)), r"\n");
        // A pure `main` runs too, and prints nothing.
        assert_eq!(
            run("def main () : () := ()\n", "", 1000),
            r#"{"ok":true,"output":""}"#
        );
    }

    /// Partial programs (docs/proposals/partial.md) run until they finish,
    /// or until the playground's limits stop them: here the output limit.
    #[test]
    fn runs_partial_programs() {
        let cat = include_str!("../../../examples/accept/cat.sw");
        assert_eq!(printed(&run(cat, "a\n\nb\n", 1000)), r"a\n\nb\n");
        let forever = "def forever (n : Nat) : {IO, Partial} () :=\n  \
                       IO.print \"tick\"\n  \
                       forever (n + 1)\n\n\
                       def main () : {IO, Partial} () := forever 0\n";
        let cut = run(forever, "", 1000);
        assert!(cut.contains("more than 1000 bytes"), "{cut}");
        assert!(cut.contains(r"tick\ntick\n"), "{cut}");
    }

    #[test]
    fn reports_why_main_cant_run() {
        let no_main = run("def x : Nat := 1\n", "", 1000);
        assert!(
            no_main.starts_with(r#"{"ok":false,"errors":"[E-NO-MAIN]"#),
            "{no_main}"
        );
        let wrong = run("def main : Nat := 1\n", "", 1000);
        assert!(
            wrong.starts_with(r#"{"ok":false,"errors":"[E-MAIN-TYPE]"#),
            "{wrong}"
        );
        let unchecked = run("def main () : {IO} () := rfl\n", "", 1000);
        assert!(
            unchecked.starts_with(r#"{"ok":false,"errors":"[E-TYPE-MISMATCH]"#),
            "{unchecked}"
        );
        // Errors before `main` starts have no output.
        assert!(!unchecked.contains("output"), "{unchecked}");
    }

    const PRINT_MANY: &str = "def printMany : Nat -> {IO} ()\n  \
                              | 0      => ()\n  \
                              | Succ n =>\n    \
                              IO.print \"ab\"\n    \
                              printMany n\n\n\
                              def main () : {IO} () := printMany 1000\n";

    #[test]
    fn stops_a_program_that_prints_too_much() {
        // 1,000 lines of 3 bytes: exactly at the limit is fine.
        let all = run(PRINT_MANY, "", 3000);
        assert!(all.starts_with(r#"{"ok":true,"#), "{all}");
        assert_eq!(printed(&all), r"ab\n".repeat(1000));
        // One byte fewer stops it, with the output up to the limit.
        let cut = run(PRINT_MANY, "", 2999);
        assert!(
            cut.starts_with(r#"{"ok":false,"errors":"[E-OUTPUT] Error: the program printed more than 2999 bytes"#),
            "{cut}"
        );
        assert!(cut.contains("while running this program"), "{cut}");
        assert_eq!(printed(&cut), r"ab\n".repeat(999) + "ab");
        // A cut through a character keeps what's before it.
        let wide = "def main () : {IO} () := IO.print \"aé\"\n";
        let cut = run(wide, "", 2);
        assert!(cut.contains("[E-OUTPUT]"), "{cut}");
        assert_eq!(printed(&cut), "a\u{FFFD}");
    }

    #[test]
    fn reports_running_out_of_resources_with_the_output_so_far() {
        let source = "def replicate : Nat -> a -> List a\n  \
                      | Zero,   x => Nil\n  \
                      | Succ n, x => Cons x (replicate n x)\n\n\
                      def main () : {IO} () :=\n  \
                      IO.print \"before\"\n  \
                      IO.print (Nat.toText (List.length (replicate 100000 1)))\n";
        let mut session = load(source).expect("it checks");
        session.elab.limits.work = 100_000;
        let result = run_loaded(session, "", 1000, MAX_READS_PAST_END);
        assert!(
            result.starts_with(r#"{"ok":false,"errors":"[E-RESOURCE]"#),
            "{result}"
        );
        assert_eq!(printed(&result), r"before\n");
    }

    /// Reads `n` lines, printing each, or `none` for `Nothing`.
    fn reads(n: usize) -> String {
        format!(
            "def textOr : Maybe Text -> Text\n  \
             | Nothing => \"none\"\n  \
             | Just t  => t\n\n\
             def readN : Nat -> {{IO}} ()\n  \
             | 0      => ()\n  \
             | Succ n =>\n    \
             IO.print (textOr (IO.readLine ()))\n    \
             readN n\n\n\
             def main () : {{IO}} () := readN {n}\n"
        )
    }

    #[test]
    fn stops_a_program_that_keeps_reading_past_the_end_of_its_input() {
        let run_reads = |n, input| run_loaded(load(&reads(n)).expect("it checks"), input, 1000, 3);
        // Two lines, the last without a line ending, then three reads past
        // the end: within the limit.
        let within = run_reads(5, "a\nb");
        assert_eq!(within, r#"{"ok":true,"output":"a\nb\nnone\nnone\nnone\n"}"#);
        let over = run_reads(6, "a\nb");
        assert!(
            over.starts_with(r#"{"ok":false,"errors":"[E-INPUT] Error: the program read past the end of its input more than 3 times"#),
            "{over}"
        );
        assert!(over.contains("while running this program"), "{over}");
        assert_eq!(printed(&over), r"a\nb\nnone\nnone\nnone\n");
        // With the playground's limit, a runaway loop stops.
        let runaway = run(&reads(1_000_000_000), "", 100_000);
        assert!(runaway.contains("[E-INPUT]"), "{runaway}");
        assert!(runaway.contains("more than 10000 times"), "{runaway}");
    }

    /// What [`run_by_line`] passes on, piece by piece, and its result.
    fn lines(source: &str, max_output: usize) -> (Vec<String>, Ran) {
        let mut pieces = Vec::new();
        let session = load(source).expect("it checks");
        let ran = run_by_line(session, "", max_output, 3, &mut |line| {
            pieces.push(line.to_string())
        });
        (pieces, ran)
    }

    #[test]
    fn streams_output_a_line_at_a_time() {
        let (pieces, ran) = lines(PRINT_MANY, 3000);
        assert_eq!(pieces, vec!["ab\n"; 1000]);
        assert_eq!(ran, Ok(Ok(())));
        // Cut at the cap: the last piece is what fits.
        let (pieces, ran) = lines(PRINT_MANY, 2999);
        assert_eq!(pieces.len(), 1000);
        assert_eq!(pieces[999], "ab");
        assert!(matches!(ran, Ok(Err(e)) if e.starts_with("[E-OUTPUT]")));
        let (pieces, _) = lines("def main () : {IO} () := IO.print \"aé\"\n", 2);
        assert_eq!(pieces, vec!["a\u{FFFD}"]);
        // Errors stop it after what was printed, and before `main` there's
        // nothing.
        let (pieces, ran) = lines(&reads(5), 1000);
        assert_eq!(pieces, vec!["none\n"; 3]);
        assert!(matches!(ran, Ok(Err(e)) if e.starts_with("[E-INPUT]")));
        let (pieces, ran) = lines("def main : Nat := 1\n", 1000);
        assert!(pieces.is_empty());
        assert!(matches!(ran, Err(e) if e.starts_with("[E-MAIN-TYPE]")));
    }

    /// The playground's examples: `(id, source)`, unescaped as a browser
    /// would read them.
    fn playground_examples() -> Vec<(&'static str, String)> {
        let page = include_str!("../../../web/index.html");
        let tag = r#"<script type="text/plain" id=""#;
        page.split(tag)
            .skip(1)
            .map(|rest| {
                let id = &rest[..rest.find('"').expect("an id")];
                let start = rest.find('>').expect("the tag ends") + 1;
                let end = rest.find("</script>").expect("the script ends");
                (id, rest[start..end].replace("<\\/", "</"))
            })
            .collect()
    }

    #[test]
    fn the_playground_examples_check_and_pass_their_tests() {
        let examples = playground_examples();
        assert!(examples.len() >= 6, "{examples:?}");
        for (id, source) in &examples {
            assert_eq!(check(source), r#"{"ok":true}"#, "{id}");
            let tests = test(source, "");
            // The tests example has one failing test on purpose.
            let failures = tests.matches(r#""passed":false"#).count();
            assert_eq!(failures, usize::from(*id == "ex-tests"), "{id}: {tests}");
        }
        let (_, main) = examples
            .iter()
            .find(|(id, _)| *id == "ex-main")
            .expect("an example with `main`");
        // The input the page fills in for it.
        assert_eq!(
            printed(&run(main, "Ada\n40\ntwo\n2\n", 100_000)),
            r#"What's your name?\nHello, Ada! Type numbers to add, one per line, and an empty line to stop.\n  total: 40\n\"two\" isn't a number; skipped\n  total: 42\nThe sum is 42. Goodbye, Ada.\n"#
        );
    }

    #[test]
    fn escapes_json_strings() {
        assert_eq!(json_string("a \"b\"\n\\c\u{1}"), r#""a \"b\"\n\\c\u0001""#);
    }
}
