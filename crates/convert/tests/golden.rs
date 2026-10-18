//! Golden tests: each `tests/golden/NAME.in.sw` (old syntax) is converted
//! and compared with `NAME.out.sw`. The output ends with the converter's
//! report as comments (arms completed for exact arity, headers without a
//! body), or is a single comment giving the reason the input can't be
//! converted. `UPDATE_GOLDEN=1 cargo test -p stitchwort-convert` rewrites the
//! outputs; review them before committing.
//!
//! TODO(switch lane): with the new-syntax parser on main, also parse each
//! output and compare its lowered tree with the input's
//! (`check_ast_equivalence`, wired to lane A's harness).

use std::path::Path;

use stitchwort_convert::{check_ast_equivalence, convert_module, elaborated_arities};

fn expected_output(input: &str) -> String {
    let arities = elaborated_arities(input).ok();
    match convert_module(input, arities.as_ref()) {
        Ok(converted) => {
            if let Some(Err(why)) = check_ast_equivalence(input, &converted.text) {
                panic!("the conversion changes the syntax tree: {why}");
            }
            let mut out = converted.text;
            let report = &converted.report;
            if !report.completions.is_empty() || !report.bodiless.is_empty() {
                if !out.ends_with('\n') {
                    out.push('\n');
                }
                out.push_str("\n-- converter report:\n");
                for c in &report.completions {
                    out.push_str(&format!("-- line {}: {}: {}\n", c.line, c.name, c.how));
                }
                for (line, name) in &report.bodiless {
                    out.push_str(&format!("-- line {line}: {name}: no body\n"));
                }
            }
            out
        }
        Err(why) => format!("-- not converted: {why}\n"),
    }
}

#[test]
fn golden_files() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/golden");
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let mut inputs: Vec<_> = std::fs::read_dir(&dir)
        .expect("tests/golden exists")
        .filter_map(|e| Some(e.ok()?.path()))
        .filter(|p| p.to_string_lossy().ends_with(".in.sw"))
        .collect();
    inputs.sort();
    assert!(!inputs.is_empty(), "no golden inputs in {}", dir.display());
    let mut failures = Vec::new();
    for input in &inputs {
        let text = std::fs::read_to_string(input).expect("readable input");
        let actual = expected_output(&text);
        let out = input.to_string_lossy().replace(".in.sw", ".out.sw");
        if update {
            std::fs::write(&out, &actual).expect("writable output");
            continue;
        }
        match std::fs::read_to_string(&out) {
            Ok(expected) if expected == actual => {}
            Ok(expected) => failures.push(format!(
                "{}:\n--- expected\n{expected}\n--- actual\n{actual}",
                input.display()
            )),
            Err(_) => failures.push(format!("{}: no {out}", input.display())),
        }
    }
    assert!(
        failures.is_empty(),
        "{} golden file(s) differ (UPDATE_GOLDEN=1 rewrites them):\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
