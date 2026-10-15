//! The browser playground's interface to the compiler. Each function takes the
//! editor's source text and returns a JSON string, so the page needs no
//! knowledge of the compiler's types.

use std::io::{self, Write};

use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_driver::render::render;
use stitchwort_driver::run::RunError;
use stitchwort_syntax::{Diagnostic, parse_expression};
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

/// Checks a program: `{"ok": true}` or `{"ok": false, "errors": "…"}`.
#[wasm_bindgen]
pub fn check(source: &str) -> String {
    match load(source) {
        Ok(_) => r#"{"ok":true}"#.into(),
        Err(errors) => failure(&errors),
    }
}

/// Runs a program's tests: `{"ok": true, "tests": [{"name": …, "passed": …,
/// "outcome": …}]}`, where the outcome is `passed`, `failed`, or what the test
/// ran out of.
#[wasm_bindgen]
pub fn test(source: &str) -> String {
    let session = match load(source) {
        Ok(session) => session,
        Err(errors) => return failure(&errors),
    };
    let tests: Vec<String> = session
        .run_tests(&Cache::disabled())
        .iter()
        .map(|r| {
            let outcome = match r.outcome {
                Outcome::Passed => "passed".to_string(),
                Outcome::Failed => "failed".to_string(),
                Outcome::OutOfResources(e) => format!("no result: {e}"),
            };
            format!(
                r#"{{"name":{},"passed":{},"outcome":{}}}"#,
                json_string(&r.name),
                r.outcome == Outcome::Passed,
                json_string(&outcome)
            )
        })
        .collect();
    format!(r#"{{"ok":true,"tests":[{}]}}"#, tests.join(","))
}

/// Evaluates an expression in the context of a program:
/// `{"ok": true, "value": "…", "type": "…"}`.
#[wasm_bindgen]
pub fn evaluate(source: &str, expr: &str) -> String {
    let mut session = match load(source) {
        Ok(session) => session,
        Err(errors) => return failure(&errors),
    };
    let file = session.sources.add("expression", expr);
    let result = parse_expression(file, expr).and_then(|e| session.elab.eval_expr(&e));
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
    let session = match load(source) {
        Ok(session) => session,
        Err(errors) => return failure(&errors),
    };
    match stitchwort_js::generate(&session.elab.globals) {
        Ok(output) => format!(
            r#"{{"ok":true,"js":{},"dts":{}}}"#,
            json_string(&output.js),
            json_string(&output.dts)
        ),
        Err(error) => failure_in(&session, &[error]),
    }
}

/// Runs a program's `main`, as `stitchwort run` does, with `input` as its
/// input: `readLine` gives its lines, then `Nothing`. Returns `{"ok": true,
/// "output": "…"}`, or `{"ok": false, "errors": "…", "output": "…"}` with
/// what was printed before the error. Each step between operations has the
/// same resource limits as a test, and the program is stopped with
/// `E-OUTPUT` once it tries to print more than `max_output` bytes.
#[wasm_bindgen]
pub fn run(source: &str, input: &str, max_output: usize) -> String {
    let session = match load(source) {
        Ok(session) => session,
        Err(errors) => return failure(&errors),
    };
    run_in(session, input, max_output)
}

/// [`run`], in a session that's already loaded.
fn run_in(mut session: Session, input: &str, max_output: usize) -> String {
    let main = match session.main() {
        Ok(main) => main,
        Err(error) => return failure_in(&session, &[error]),
    };
    let mut output = Capped {
        bytes: Vec::new(),
        max: max_output,
        full: false,
    };
    let result = session.run_main(&main, &mut input.as_bytes(), &mut output);
    // The cap can cut a character in two.
    let printed = json_string(&String::from_utf8_lossy(&output.bytes));
    match result {
        Ok(()) => format!(r#"{{"ok":true,"output":{printed}}}"#),
        Err(error) => {
            let error = match error {
                RunError::Write(_) if output.full => Diagnostic::error(
                    "E-OUTPUT",
                    format!(
                        "the program printed more than {max_output} bytes, the playground's limit"
                    ),
                )
                .with_label(main.span, "while running this program"),
                error => error.diagnostic(&main),
            };
            format!(
                r#"{{"ok":false,"errors":{},"output":{printed}}}"#,
                json_string(&rendered(&session, &[error]))
            )
        }
    }
}

/// Output that keeps at most `max` bytes, and fails once more is written.
struct Capped {
    bytes: Vec<u8>,
    max: usize,
    full: bool,
}

impl Write for Capped {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let room = self.max - self.bytes.len();
        if room == 0 && !buf.is_empty() {
            self.full = true;
            return Err(io::Error::other("the output budget is used up"));
        }
        let n = room.min(buf.len());
        self.bytes.extend_from_slice(&buf[..n]);
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// A session with `source` loaded, or its errors rendered as text.
fn load(source: &str) -> Result<Session, String> {
    let mut session = Session::new();
    session.elab.limits = session_limits();
    match session.load(FILE, source) {
        Ok(_) => Ok(session),
        Err(errors) => Err(rendered(&session, &errors)),
    }
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
    fn reports_success_errors_tests_values_and_extracted_code() {
        assert_eq!(check("x : Nat\nx = 1\n"), r#"{"ok":true}"#);
        let errors = check("x : Nat\nx = rfl\n");
        assert!(
            errors.starts_with(r#"{"ok":false,"errors":"[E-TYPE-MISMATCH]"#),
            "{errors}"
        );
        assert_eq!(
            test("test \"one\" = True\ntest \"two\" = False\n"),
            r#"{"ok":true,"tests":[{"name":"one","passed":true,"outcome":"passed"},{"name":"two","passed":false,"outcome":"failed"}]}"#
        );
        assert_eq!(
            evaluate("double : Nat -> Nat\ndouble n = n + n\n", "double 4"),
            r#"{"ok":true,"value":"8","type":"Nat"}"#
        );
        let js = extract("export\nf : Nat -> Nat\nf n = n\n");
        assert!(js.contains(r#""js":"// Generated by stitchwort"#), "{js}");
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
        let echo = "textOr : Text -> Maybe Text -> Text\ntextOr d Nothing  = d\n\
                    textOr d (Just t) = t\n\nmain : () -> {IO} ()\nmain u =\n  \
                    print (textOr \"none\" (readLine ()))\n  print (textOr \"none\" (readLine ()))\n  \
                    print (textOr \"none\" (readLine ()))\n";
        assert_eq!(printed(&run(echo, "\nlast", 1000)), r"\nlast\nnone\n");
        // A pure `main` runs too, and prints nothing.
        assert_eq!(
            run("main : () -> ()\nmain u = ()\n", "", 1000),
            r#"{"ok":true,"output":""}"#
        );
    }

    #[test]
    fn reports_why_main_cant_run() {
        let no_main = run("x : Nat\nx = 1\n", "", 1000);
        assert!(
            no_main.starts_with(r#"{"ok":false,"errors":"[E-NO-MAIN]"#),
            "{no_main}"
        );
        let wrong = run("main : Nat\nmain = 1\n", "", 1000);
        assert!(
            wrong.starts_with(r#"{"ok":false,"errors":"[E-MAIN-TYPE]"#),
            "{wrong}"
        );
        let unchecked = run("main : () -> {IO} ()\nmain u = rfl\n", "", 1000);
        assert!(
            unchecked.starts_with(r#"{"ok":false,"errors":"[E-TYPE-MISMATCH]"#),
            "{unchecked}"
        );
        // Errors before `main` starts have no output.
        assert!(!unchecked.contains("output"), "{unchecked}");
    }

    const PRINT_MANY: &str = "printMany : Nat -> {IO} ()\nprintMany 0        = ()\n\
                              printMany (Succ n) =\n  print \"ab\"\n  printMany n\n\n\
                              main : () -> {IO} ()\nmain u = printMany 1000\n";

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
        let wide = "main : () -> {IO} ()\nmain u = print \"a\u{E9}\"\n";
        let cut = run(wide, "", 2);
        assert!(cut.contains("[E-OUTPUT]"), "{cut}");
        assert_eq!(printed(&cut), "a\u{FFFD}");
    }

    #[test]
    fn reports_running_out_of_resources_with_the_output_so_far() {
        let source = "replicate : Nat -> a -> List a\nreplicate Zero     x = Nil\n\
                      replicate (Succ n) x = Cons x (replicate n x)\n\n\
                      main : () -> {IO} ()\nmain u =\n  print \"before\"\n  \
                      print (natToText (length (replicate 100000 1)))\n";
        let mut session = load(source).expect("it checks");
        session.elab.limits.work = 100_000;
        let result = run_in(session, "", 1000);
        assert!(
            result.starts_with(r#"{"ok":false,"errors":"[E-RESOURCE]"#),
            "{result}"
        );
        assert_eq!(printed(&result), r"before\n");
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
            let tests = test(source);
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
