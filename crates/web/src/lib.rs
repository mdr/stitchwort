//! The browser playground's interface to the compiler. Each function takes the
//! editor's source text and returns a JSON string, so the page needs no
//! knowledge of the compiler's types.

use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_driver::render::render;
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

    #[test]
    fn escapes_json_strings() {
        assert_eq!(json_string("a \"b\"\n\\c\u{1}"), r#""a \"b\"\n\\c\u0001""#);
    }
}
