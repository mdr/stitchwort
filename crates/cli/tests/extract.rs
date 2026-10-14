//! Differential tests for JS extraction (DESIGN.md §12).
//!
//! For each `examples/extract/*.sw`, every `-- run: f arg1 arg2` line is
//! evaluated twice: by the reference evaluator, and by calling the generated
//! JS under Node. The two results must agree through the boundary encoding.
//! Requires `node` on the PATH (the Nix dev shell provides it).

use std::path::Path;
use std::process::Command;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_core::Term;
use stitchwort_core::value::eval;
use stitchwort_js::{boundary_literal, exportable};
use stitchwort_syntax::parse_expression;

const RUN: &str = "-- run:";

#[test]
fn extracted_code_agrees_with_the_reference_evaluator() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/extract");
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("examples/extract exists")
        .map(|e| e.expect("readable entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no extraction examples found");
    for path in files {
        check_file(&path);
    }
}

fn check_file(path: &Path) {
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let text = std::fs::read_to_string(path).expect("readable example");
    let mut session = Session::new();
    if let Err(diagnostics) = session.load(&name, &text) {
        let rendered: String = diagnostics
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect();
        panic!("{name} doesn't check:\n{rendered}");
    }
    let output = stitchwort_js::generate(&session.elab.globals).expect("extraction succeeds");

    // Each run line becomes a pair: the JS result and the reference result.
    let mut cases = Vec::new();
    let mut script = String::from(
        "import * as m from \"./module.mjs\";\n\
         const canon = (v) => JSON.stringify(v, (_, x) => typeof x === \"bigint\" ? `${x}n` : x);\n\
         const results = [];\n",
    );
    for line in text.lines().filter_map(|l| l.strip_prefix(RUN)) {
        let source = line.trim();
        let (call, expected) = reference(&mut session, source);
        script.push_str(&format!(
            "results.push([canon(m.{call}), canon({expected})]);\n"
        ));
        cases.push(source.to_string());
    }
    assert!(!cases.is_empty(), "{name} has no `{RUN}` lines");
    script.push_str("console.log(JSON.stringify(results));\n");

    let dir = std::env::temp_dir().join(format!(
        "stitchwort-extract-{}-{}",
        std::process::id(),
        name.trim_end_matches(".sw")
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    std::fs::write(dir.join("module.mjs"), &output.js).expect("write module");
    std::fs::write(dir.join("test.mjs"), &script).expect("write script");
    let result = Command::new("node")
        .arg("test.mjs")
        .current_dir(&dir)
        .output()
        .expect("run `node` (is it on the PATH? `nix develop` provides it)");
    assert!(
        result.status.success(),
        "node failed for {name}:\n{}\n--- module.mjs ---\n{}",
        String::from_utf8_lossy(&result.stderr),
        output.js
    );
    let stdout = String::from_utf8_lossy(&result.stdout);
    let results: Vec<(String, String)> = parse_pairs(stdout.trim());
    assert_eq!(results.len(), cases.len());
    for (case, (js, reference)) in cases.iter().zip(results) {
        assert_eq!(
            js, reference,
            "{name}: `{case}` gives {js} in JS but {reference} in the reference evaluator"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// For `f a b`: the JS call `f(<a>, <b>)`, and the reference result as a JS
/// literal, both in the boundary encoding.
fn reference(session: &mut Session, source: &str) -> (String, String) {
    let file = session.sources.add("<run>", source);
    let expr = parse_expression(file, source).expect("run line parses");
    let (term, _) = session
        .elab
        .infer_expr(&expr)
        .unwrap_or_else(|d| panic!("`{source}` doesn't check: {}", d.message));
    let g = &session.elab.globals;
    let (head, args) = term.spine();
    let Term::Def(id) = head else {
        panic!("`{source}` must be a call to an exported function");
    };
    let sig = exportable(g, *id).unwrap_or_else(|d| panic!("{}", d.message));
    let js_args: Vec<String> = args
        .iter()
        .zip(&sig.params)
        .map(|(arg, (_, b))| {
            boundary_literal(g, b, &eval(g, &[], arg)).expect("argument evaluates")
        })
        .collect();
    let expected =
        boundary_literal(g, &sig.result, &eval(g, &[], &term)).expect("result evaluates");
    (format!("{}({})", sig.name, js_args.join(", ")), expected)
}

/// Parses `[["a","b"],["c","d"]]` as printed by the script. The strings are
/// themselves JSON, compared as opaque text.
fn parse_pairs(json: &str) -> Vec<(String, String)> {
    let mut strings = Vec::new();
    let mut chars = json.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' {
            let mut s = String::new();
            while let Some(c) = chars.next() {
                match c {
                    '\\' => s.push(chars.next().expect("escaped character")),
                    '"' => break,
                    c => s.push(c),
                }
            }
            strings.push(s);
        }
    }
    strings
        .chunks(2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect()
}
