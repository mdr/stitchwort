//! Differential tests for JS extraction (DESIGN.md §12): the generated JS must
//! agree with the reference evaluator, through the boundary encoding.
//!
//! - Every `-- run: f arg1 arg2` line in `examples/extract/*.sw` is checked.
//! - Every `-- rejects: f arg1 arg2` line must be refused by the generated
//!   precondition checks, with a `StitchwortInputError`.
//! - Every export is also called on random inputs generated from its boundary
//!   types, from a fixed seed so failures are reproducible. Where the reference
//!   evaluator's precondition check says no, JS must refuse the input.
//!
//! Requires `node` on the PATH (the Nix dev shell provides it).

use std::path::{Path, PathBuf};
use std::process::Command;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_core::value::{apply, eval, force};
use stitchwort_core::{DataId, DefId, Globals, Limits, Term, Value};
use stitchwort_js::{Boundary, boundary_literal, exportable, field_boundaries};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::parse_expression;

const RUN: &str = "-- run:";
const REJECTS: &str = "-- rejects:";
/// What a case expects when the input must be refused.
const REJECTED: &str = "\"rejected\"";
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
        for line in text.lines().filter_map(|l| l.strip_prefix(REJECTS)) {
            let source = line.trim();
            cases.push(Case {
                description: source.to_string(),
                call: rejected_call(&mut session, source),
                expected: REJECTED.into(),
            });
        }
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
            let arity = sig.params.len() + sig.checks.len();
            for _ in 0..RANDOM_CASES_PER_EXPORT {
                let data: Vec<Value> = sig
                    .params
                    .iter()
                    .map(|(_, b)| random_value(g, b, &mut rng, 3))
                    .collect();
                // All the arguments in order, with proofs as placeholders (they're
                // erased, so their value doesn't matter), and whether each
                // precondition holds according to the reference evaluator.
                let mut args = Vec::new();
                let mut accepted = true;
                for position in 0..arity {
                    if let Some(i) = sig.param_positions.iter().position(|p| *p == position) {
                        args.push(data[i].clone());
                    } else {
                        let check = sig.checks.iter().find(|c| c.position == position).unwrap();
                        let decision = force(g, eval(g, &args, &check.decision).unwrap()).unwrap();
                        accepted &= matches!(decision, Value::Ctor(_, 0, _));
                        args.push(Value::Refl);
                    }
                }
                let literals: Vec<String> = data
                    .iter()
                    .zip(&sig.params)
                    .map(|(a, (_, b))| boundary_literal(g, b, a).expect("argument encodes"))
                    .collect();
                let call = format!("{}({})", sig.name, literals.join(", "));
                let expected = if accepted {
                    let result = args
                        .into_iter()
                        .fold(eval(g, &[], &Term::Def(id)).unwrap(), |f, a| {
                            apply(g, f, a).unwrap()
                        });
                    boundary_literal(g, &sig.result, &result).expect("result evaluates")
                } else {
                    REJECTED.into()
                };
                cases.push(Case {
                    description: call.clone(),
                    call,
                    expected,
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
        let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
            .expect("extraction succeeds");
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
    let output = stitchwort_js::generate(g, Limits::default()).expect("extraction succeeds");
    let mut script = String::from(
        "import * as m from \"./module.mjs\";\n\
         const canon = (v) => JSON.stringify(v, (_, x) => typeof x === \"bigint\" ? `${x}n` : x);\n\
         const results = [];\n\
         const attempt = (f) => {\n\
           try { return canon(f()); }\n\
           catch (e) { if (e instanceof m.StitchwortInputError) return canon(\"rejected\"); throw e; }\n\
         };\n",
    );
    for case in cases {
        script.push_str(&format!(
            "results.push([attempt(() => m.{}), canon({})]);\n",
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
    // Proof arguments aren't passed to JS.
    let js_args: Vec<String> = sig
        .params
        .iter()
        .zip(&sig.param_positions)
        .map(|((_, b), position)| {
            boundary_literal(g, b, &eval(g, &[], args[*position]).unwrap())
                .expect("argument evaluates")
        })
        .collect();
    let expected =
        boundary_literal(g, &sig.result, &eval(g, &[], &term).unwrap()).expect("result evaluates");
    (format!("{}({})", sig.name, js_args.join(", ")), expected)
}

/// For `f a b`, a JS call `f(<a>, <b>)` that's expected to be refused. The
/// call itself wouldn't type-check (its precondition fails), so each argument
/// is evaluated separately.
fn rejected_call(session: &mut Session, source: &str) -> String {
    let file = session.sources.add("<rejects>", source);
    let expr = parse_expression(file, source).expect("rejects line parses");
    let mut args = Vec::new();
    let mut head = &expr;
    while let Expr::App(f, a) = head {
        args.push(a.as_ref());
        head = f;
    }
    args.reverse();
    let Expr::Var(name) = head else {
        panic!("`{source}` must be a call to an exported function");
    };
    let g = &session.elab.globals;
    let id = (0..g.defs.len())
        .map(DefId)
        .find(|id| *g.def(*id).name == *name.text)
        .unwrap_or_else(|| panic!("no export called `{}`", name.text));
    let sig = exportable(g, id).unwrap_or_else(|d| panic!("{}", d.message));
    assert_eq!(
        args.len(),
        sig.params.len(),
        "`{source}`: wrong number of arguments"
    );
    let literals: Vec<String> = args
        .iter()
        .zip(&sig.params)
        .map(|(arg, (_, b))| {
            let (term, _) = session
                .elab
                .infer_expr(arg)
                .unwrap_or_else(|d| panic!("`{source}`: {}", d.message));
            let g = &session.elab.globals;
            boundary_literal(g, b, &eval(g, &[], &term).unwrap()).expect("argument evaluates")
        })
        .collect();
    format!("{}({})", sig.name, literals.join(", "))
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
        Boundary::Bool => Value::Ctor(named("Bool"), rng.below(2), vec![].into()),
        Boundary::Nat => (0..rng.below(8))
            .fold(Value::Ctor(named("Nat"), 0, vec![].into()), |n, _| {
                Value::Ctor(named("Nat"), 1, vec![n].into())
            }),
        Boundary::List(elem) => {
            let len = if depth == 0 { 0 } else { rng.below(5) };
            (0..len).fold(Value::Ctor(named("List"), 0, vec![].into()), |tail, _| {
                let head = random_value(g, elem, rng, depth.saturating_sub(1));
                Value::Ctor(named("List"), 1, vec![head, tail].into())
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

/// DESIGN.md §12: decoders copy their input, reading each property once, and
/// refuse inputs that contain themselves rather than recursing forever.
#[test]
fn decoders_refuse_cycles_and_read_each_property_once() {
    let examples = examples();
    let (_, _, trees) = examples
        .iter()
        .find(|(n, _, _)| n == "trees.sw")
        .expect("trees.sw");
    let (_, _, shapes) = examples
        .iter()
        .find(|(n, _, _)| n == "shapes.sw")
        .expect("shapes.sw");
    let script = r#"
import * as trees from "./trees.mjs";
import * as shapes from "./shapes.mjs";
import assert from "node:assert/strict";

// A tree that contains itself is refused cleanly.
const loop = { tag: "Node", left: null, right: { tag: "Leaf" } };
loop.left = loop;
assert.throws(() => trees.leaves(loop), (e) => e instanceof trees.StitchwortInputError && /contains itself/.test(e.message));

// Sharing without a cycle is fine: both children are the same object.
const leaf = { tag: "Leaf" };
assert.equal(trees.leaves({ tag: "Node", left: leaf, right: leaf }), 2n);

// Each property is read exactly once, so a getter can't change its answer
// between validation and use.
let reads = 0;
const sneaky = { tag: "Square", get side() { reads += 1; return reads === 1 ? 3n : 1000n; } };
assert.equal(shapes.area(sneaky), 9n);
assert.equal(reads, 1);

// Mutating the input after the call can't affect a result already computed,
// and a list is copied before use.
const list = [{ tag: "Square", side: 2n }];
const result = shapes.areas(list);
list[0].side = 100n;
assert.deepEqual(result, [4n]);

// Wrong shapes are refused with a path to the problem.
assert.throws(() => shapes.area({ tag: "Circle" }), /unknown tag Circle/);
assert.throws(() => shapes.areas([{ tag: "Rect", width: 1n, height: -1n }]), /\[0\]\.height: expected a non-negative bigint/);
console.log("ok");
"#;
    let dir = std::env::temp_dir().join(format!("stitchwort-decoders-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    for (file, session) in [("trees.mjs", trees), ("shapes.mjs", shapes)] {
        let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
            .expect("extraction succeeds");
        std::fs::write(dir.join(file), output.js).expect("write module");
    }
    std::fs::write(dir.join("test.mjs"), script).expect("write script");
    let result = Command::new("node")
        .arg("test.mjs")
        .current_dir(&dir)
        .output()
        .expect("run `node`");
    assert!(
        result.status.success() && String::from_utf8_lossy(&result.stdout).trim() == "ok",
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let _ = std::fs::remove_dir_all(&dir);
}
