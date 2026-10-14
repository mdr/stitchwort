//! Differential tests for JS extraction (DESIGN.md §12): the generated JS must
//! agree with the reference evaluator, through the boundary encoding.
//!
//! - Every `-- run: f arg1 arg2` line in `examples/extract/*.sw` is checked.
//! - Every export is also called on random inputs generated from its boundary
//!   types, from a fixed seed so failures are reproducible.
//!
//! Requires `node` on the PATH (the Nix dev shell provides it).

use std::path::{Path, PathBuf};
use std::process::Command;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_core::value::{apply, eval};
use stitchwort_core::{DataId, DefId, Globals, Term, Value};
use stitchwort_js::{Boundary, boundary_literal, exportable, field_boundaries};
use stitchwort_syntax::parse_expression;

const RUN: &str = "-- run:";
const RANDOM_CASES_PER_EXPORT: usize = 100;

#[test]
fn run_lines_agree_with_the_reference_evaluator() {
    for (name, text, mut session) in examples() {
        let mut cases = Vec::new();
        for line in text.lines().filter_map(|l| l.strip_prefix(RUN)) {
            let source = line.trim();
            let (call, expected) = run_line(&mut session, source);
            cases.push(Case {
                description: source.to_string(),
                call,
                expected,
            });
        }
        assert!(!cases.is_empty(), "{name} has no `{RUN}` lines");
        check_in_node(&name, &session.elab.globals, &cases);
    }
}

#[test]
fn random_inputs_agree_with_the_reference_evaluator() {
    let mut rng = Rng(0x0dd5_eed5_ca1e_d0c5);
    for (name, _, session) in examples() {
        let g = &session.elab.globals;
        let mut cases = Vec::new();
        for id in (0..g.defs.len()).map(DefId).filter(|id| g.def(*id).export) {
            let sig = exportable(g, id).expect("exports check");
            for _ in 0..RANDOM_CASES_PER_EXPORT {
                let args: Vec<Value> = sig
                    .params
                    .iter()
                    .map(|(_, b)| random_value(g, b, &mut rng, 3))
                    .collect();
                let result = args
                    .iter()
                    .fold(eval(g, &[], &Term::Def(id)), |f, a| apply(g, f, a.clone()));
                let literals: Vec<String> = args
                    .iter()
                    .zip(&sig.params)
                    .map(|(a, (_, b))| boundary_literal(g, b, a).expect("argument encodes"))
                    .collect();
                let call = format!("{}({})", sig.name, literals.join(", "));
                cases.push(Case {
                    description: call.clone(),
                    call,
                    expected: boundary_literal(g, &sig.result, &result).expect("result evaluates"),
                });
            }
        }
        check_in_node(&name, g, &cases);
    }
}

/// The generated module and declarations are snapshot-tested (so any change to
/// the output shows up in review), and the declarations must type-check.
#[test]
fn generated_code_is_stable_and_the_declarations_type_check() {
    for (name, _, session) in examples() {
        let output = stitchwort_js::generate(&session.elab.globals).expect("extraction succeeds");
        let stem = name.trim_end_matches(".sw");
        insta::assert_snapshot!(format!("{stem}.js"), output.js);
        insta::assert_snapshot!(format!("{stem}.d.ts"), output.dts);

        let dir =
            std::env::temp_dir().join(format!("stitchwort-dts-{}-{stem}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        std::fs::write(dir.join("module.d.ts"), &output.dts).expect("write declarations");
        let result = Command::new("tsc")
            .args(["--noEmit", "--strict", "module.d.ts"])
            .current_dir(&dir)
            .output()
            .expect("run `tsc` (is it on the PATH? `nix develop` provides it)");
        assert!(
            result.status.success(),
            "{name}: the generated declarations don't type-check:\n{}{}\n--- module.d.ts ---\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr),
            output.dts
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}

struct Case {
    description: String,
    /// A JS call to an export, with arguments in the boundary encoding.
    call: String,
    /// The reference evaluator's result, as a JS literal.
    expected: String,
}

/// Each extraction example, checked.
fn examples() -> Vec<(String, String, Session)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/extract");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("examples/extract exists")
        .map(|e| e.expect("readable entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no extraction examples found");
    files
        .into_iter()
        .map(|path| {
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            let text = std::fs::read_to_string(&path).expect("readable example");
            let mut session = Session::new();
            if let Err(diagnostics) = session.load(&name, &text) {
                let rendered: String = diagnostics
                    .iter()
                    .map(|d| render(&session.sources, d, false))
                    .collect();
                panic!("{name} doesn't check:\n{rendered}");
            }
            (name, text, session)
        })
        .collect()
}

/// Runs every case against the generated JS under Node, and compares.
fn check_in_node(name: &str, g: &Globals, cases: &[Case]) {
    let output = stitchwort_js::generate(g).expect("extraction succeeds");
    let mut script = String::from(
        "import * as m from \"./module.mjs\";\n\
         const canon = (v) => JSON.stringify(v, (_, x) => typeof x === \"bigint\" ? `${x}n` : x);\n\
         const results = [];\n",
    );
    for case in cases {
        script.push_str(&format!(
            "results.push([canon(m.{}), canon({})]);\n",
            case.call, case.expected
        ));
    }
    script.push_str("console.log(JSON.stringify(results));\n");

    let dir = std::env::temp_dir().join(format!(
        "stitchwort-extract-{}-{}-{}",
        std::process::id(),
        name.trim_end_matches(".sw"),
        cases.len()
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
    let results = parse_pairs(stdout.trim());
    assert_eq!(results.len(), cases.len());
    for (case, (js, reference)) in cases.iter().zip(results) {
        assert_eq!(
            js, reference,
            "{name}: `{}` gives {js} in JS but {reference} in the reference evaluator",
            case.description
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// For `f a b`: the JS call `f(<a>, <b>)`, and the reference result as a JS
/// literal, both in the boundary encoding.
fn run_line(session: &mut Session, source: &str) -> (String, String) {
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

/// xorshift64*: tiny and deterministic.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        (self.0.wrapping_mul(0x2545_f491_4f6c_dd1d) % n as u64) as usize
    }
}

/// A random value of a boundary type. `depth` bounds recursive data types.
fn random_value(g: &Globals, b: &Boundary, rng: &mut Rng, depth: usize) -> Value {
    let named = |name: &str| -> DataId { g.find_data(name).expect("prelude type") };
    match b {
        Boundary::Nat => (0..rng.below(8)).fold(Value::Ctor(named("Nat"), 0, vec![]), |n, _| {
            Value::Ctor(named("Nat"), 1, vec![n])
        }),
        Boundary::List(elem) => {
            let len = if depth == 0 { 0 } else { rng.below(5) };
            (0..len).fold(Value::Ctor(named("List"), 0, vec![]), |tail, _| {
                let head = random_value(g, elem, rng, depth.saturating_sub(1));
                Value::Ctor(named("List"), 1, vec![head, tail])
            })
        }
        Boundary::Data(d) => {
            let ctors = field_boundaries(g, *d);
            // Near the depth limit, prefer constructors without recursive fields.
            let candidates: Vec<usize> = (0..ctors.len())
                .filter(|&c| depth > 0 || ctors[c].iter().all(|(_, f)| *f != Boundary::Data(*d)))
                .collect();
            let candidates = if candidates.is_empty() {
                (0..ctors.len()).collect()
            } else {
                candidates
            };
            let c = candidates[rng.below(candidates.len())];
            let fields = ctors[c]
                .iter()
                .map(|(_, f)| random_value(g, f, rng, depth.saturating_sub(1)))
                .collect();
            Value::Ctor(*d, c, fields)
        }
    }
}

/// Parses `[["a","b"],["c","d"]]` as printed by the script. The strings are
/// themselves JSON, compared as opaque text.
fn parse_pairs(json: &str) -> Vec<(String, String)> {
    let mut strings = Vec::new();
    let mut chars = json.chars();
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
