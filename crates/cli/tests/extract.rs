//! Differential tests for JS extraction (DESIGN.md §12): the generated JS must
//! agree with the reference evaluator, through the boundary encoding.
//!
//! - Every `-- run: f arg1 arg2` line in `examples/extract/*.sw` is checked.
//! - Every `-- rejects: f arg1 arg2` line must be refused by the generated
//!   precondition checks, with a `StitchwortInputError`.
//! - Every export is also called on random inputs generated from its boundary
//!   types, from a fixed seed so failures are reproducible. Where the reference
//!   evaluator's precondition check says no, JS must refuse the input.
//! - Both are run against the generated JS with native text operations, and
//!   with every text operation compiled from its list definition instead.
//!
//! Requires `node` on the PATH (the Nix dev shell provides it).

use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_core::hash::data_hash;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{apply, eval, force};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Limits, Term, Value};
use stitchwort_js::{
    Boundary, Options, boundary_literal, exportable, field_boundaries, js_string_literal,
};
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
                // Records' proof fields must hold, as their decision
                // procedures say (examples/extract/records.sw).
                let mut accepted = data
                    .iter()
                    .zip(&sig.params)
                    .all(|(v, (_, b))| proofs_hold(g, b, v));
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
            .args([
                "--noEmit",
                "--strict",
                "--exactOptionalPropertyTypes",
                "module.d.ts",
            ])
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

/// Text as a list, every text operation compiled from its definition.
const LIST_TEXT: Options = Options {
    native_text: false,
    native_int: true,
};

/// `Int` as its constructors inside generated code, every integer operation
/// compiled from its definition.
const DATA_INT: Options = Options {
    native_text: true,
    native_int: false,
};

/// Runs every case against the generated JS under Node, and compares, with
/// native text operations and without.
fn check_in_node(name: &str, g: &Globals, cases: &[Case]) {
    for options in [Options::default(), LIST_TEXT, DATA_INT] {
        check_in_node_with(name, g, cases, options);
    }
}

fn check_in_node_with(name: &str, g: &Globals, cases: &[Case], options: Options) {
    let output =
        stitchwort_js::generate_with(g, Limits::default(), options).expect("extraction succeeds");
    let mut script = String::from(
        "import * as m from \"./module.mjs\";\n\
         const canon = (v) => JSON.stringify(v, (_, x) => typeof x === \"bigint\" ? `${x}n` : x) ?? \"undefined\";\n\
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
        "stitchwort-extract-{}-{}-{}-{}-{}",
        std::process::id(),
        name.trim_end_matches(".sw"),
        cases.len(),
        options.native_text,
        options.native_int
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
        "node failed for {name} ({options:?}):\n{}\n--- module.mjs ---\n{}",
        String::from_utf8_lossy(&result.stderr),
        output.js
    );
    let stdout = String::from_utf8_lossy(&result.stdout);
    let results = parse_pairs(stdout.trim());
    assert_eq!(results.len(), cases.len());
    for (case, (js, reference)) in cases.iter().zip(results) {
        assert_eq!(
            js, reference,
            "{name}: `{}` gives {js} in JS ({options:?}) but {reference} in the reference evaluator",
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
        // Mostly small, sometimes around ±2^64 and ±2^128.
        Boundary::Int => {
            let magnitude = match rng.below(4) {
                0 => {
                    (BigUint::from(1u32) << (64 * (1 + rng.below(2)))) - BigUint::from(rng.below(3))
                }
                _ => BigUint::from(rng.below(13)),
            };
            Value::Ctor(
                named("Int"),
                rng.below(2),
                vec![Value::Nat(std::rc::Rc::new(magnitude))].into(),
            )
        }
        // Mostly small, sometimes at or just beyond the bounds, where the
        // generated decoder must refuse what the proof field says doesn't hold.
        Boundary::SafeNat | Boundary::SafeInt => {
            let magnitude = match rng.below(4) {
                0 => BigUint::from(MAX_SAFE) + BigUint::from(rng.below(3)) - BigUint::from(1u32),
                _ => BigUint::from(rng.below(13)),
            };
            let nat = Value::Nat(std::rc::Rc::new(magnitude));
            let (record, value) = if matches!(b, Boundary::SafeNat) {
                ("SafeNat", nat)
            } else {
                (
                    "SafeInt",
                    Value::Ctor(named("Int"), rng.below(2), vec![nat].into()),
                )
            };
            Value::Ctor(named(record), 0, vec![value, Value::Refl].into())
        }
        Boundary::Char => random_char(g, rng),
        Boundary::Text => {
            let len = rng.below(7);
            let chars = (0..len).fold(Value::Ctor(named("List"), 0, vec![].into()), |tail, _| {
                Value::Ctor(named("List"), 1, vec![random_char(g, rng), tail].into())
            });
            Value::Ctor(named("Text"), 0, vec![chars].into())
        }
        Boundary::Data(d, args) => {
            let ctors = field_boundaries(g, *d, args);
            // Near the depth limit, prefer constructors without recursive fields.
            let recursive = |f: &Boundary| matches!(f, Boundary::Data(e, _) if e == d);
            let candidates: Vec<usize> = (0..ctors.len())
                .filter(|&c| depth > 0 || !ctors[c].iter().any(|(_, f)| recursive(f)))
                .collect();
            let candidates = if candidates.is_empty() {
                (0..ctors.len()).collect()
            } else {
                candidates
            };
            let c = candidates[rng.below(candidates.len())];
            // Erased fields (a record's proofs) are placeholders: they're
            // checked by the record's decision procedures, not read.
            let mut runtime = ctors[c].iter();
            let fields = g.data(*d).ctors[c]
                .field_erased
                .iter()
                .map(|erased| match erased {
                    true => Value::Refl,
                    false => {
                        let (_, f) = runtime.next().expect("a runtime field");
                        random_value(g, f, rng, depth.saturating_sub(1))
                    }
                })
                .collect();
            Value::Ctor(*d, c, fields)
        }
        Boundary::Option(d, inner) => match rng.below(2) {
            0 => Value::Ctor(*d, 0, vec![].into()),
            _ => Value::Ctor(
                *d,
                1,
                vec![random_value(g, inner, rng, depth.saturating_sub(1))].into(),
            ),
        },
        Boundary::Param(_) => panic!("a boundary type of an export has no parameters"),
    }
}

/// Whether the proof fields of every record in `value`, of boundary type
/// `b`, hold according to their decision procedures, run by the reference
/// evaluator: what the generated decoder checks.
fn proofs_hold(g: &Globals, b: &Boundary, value: &Value) -> bool {
    match (b, value) {
        (Boundary::List(elem), Value::Ctor(_, 1, fields)) => {
            proofs_hold(g, elem, &fields[0]) && proofs_hold(g, b, &fields[1])
        }
        (Boundary::Option(_, inner), Value::Ctor(_, c, fields)) => {
            *c == 0 || proofs_hold(g, inner, &fields[0])
        }
        (Boundary::Data(d, args), Value::Ctor(_, c, fields)) => {
            let data = g.data(*d);
            // Parameters are types, which nothing at runtime looks at.
            let params: Vec<Value> = data.params.iter().map(|_| Value::Refl).collect();
            let checked = data.validators.iter().filter(|v| v.ctor == *c).all(|v| {
                let mut env = params.clone();
                env.extend(fields[..v.field].iter().cloned());
                let decision = force(g, eval(g, &env, &v.decision).unwrap()).unwrap();
                matches!(decision, Value::Ctor(_, 0, _))
            });
            let runtime = fields
                .iter()
                .zip(&data.ctors[*c].field_erased)
                .filter(|(_, erased)| !**erased);
            checked
                && field_boundaries(g, *d, args)[*c]
                    .iter()
                    .zip(runtime)
                    .all(|((_, fb), (v, _))| proofs_hold(g, fb, v))
        }
        // The bound the type's proof field states.
        (Boundary::SafeNat, Value::Ctor(_, _, fields)) => {
            nat_of(g, &fields[0]) <= BigUint::from(MAX_SAFE)
        }
        (Boundary::SafeInt, Value::Ctor(_, _, fields)) => match &fields[0] {
            // `OfNat n` is `n`, and `NegSucc n` is `-n - 1`, so both are in
            // bounds up to 2^53 - 1 in magnitude.
            Value::Ctor(_, 0, inner) => nat_of(g, &inner[0]) <= BigUint::from(MAX_SAFE),
            Value::Ctor(_, _, inner) => nat_of(g, &inner[0]) < BigUint::from(MAX_SAFE),
            _ => panic!("an evaluated `Int`"),
        },
        _ => true,
    }
}

/// 2^53 - 1: the largest whole number a JS `number` holds exactly.
const MAX_SAFE: u64 = 9_007_199_254_740_991;

fn nat_of(g: &Globals, v: &Value) -> BigUint {
    stitchwort_core::native::as_nat(g, v)
        .expect("evaluates")
        .expect("an evaluated `Nat`")
}

/// Characters where JavaScript's strings and Stitchwort's text disagree
/// about length, order or iteration, and ordinary ones for contrast.
const AWKWARD_CHARS: &[char] = &[
    'a',
    'Z',
    '0',
    '7',
    ' ',
    ',',
    '\t',
    '\n',
    '\r',
    '\0',
    'é',
    '\u{301}',
    '\u{d7ff}',
    '\u{e000}',
    '\u{fdd0}',
    '\u{fffe}',
    '\u{ffff}',
    '\u{10000}',
    '\u{1f600}',
    '\u{10ffff}',
    '\u{2028}',
    '\u{a0}',
];

/// A random `Char`, built as the evaluator builds one (its proof is erased
/// at runtime, so a placeholder will do).
fn random_char(g: &Globals, rng: &mut Rng) -> Value {
    let c = AWKWARD_CHARS[rng.below(AWKWARD_CHARS.len())];
    let code = Value::Nat(std::rc::Rc::new(BigUint::from(u32::from(c))));
    Value::Ctor(
        g.find_data("Char").expect("prelude type"),
        0,
        vec![code, Value::Refl].into(),
    )
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
    let trees = example(&examples, "trees.sw");
    let shapes = example(&examples, "shapes.sw");
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
assert.throws(() => shapes.area({ tag: "Circle" }), / arg0: unknown tag "Circle"; expected "Square" or "Rect"$/);
assert.throws(() => shapes.area({}), / arg0: no tag; expected "Square" or "Rect"$/);
assert.throws(() => shapes.area({ tag: "x".repeat(1000) }), (e) => e.message.length < 120);
// An inherited property isn't a tag.
assert.throws(() => shapes.area({ tag: "toString" }), /unknown tag "toString"/);
assert.throws(() => shapes.areas([{ tag: "Rect", width: 1n, height: -1n }]), /\[0\]\.height: expected a non-negative bigint/);
console.log("ok");
"#;
    run_script(
        "decoders",
        &[("trees.mjs", trees), ("shapes.mjs", shapes)],
        script,
    );
}

/// DESIGN.md §12: decoders read only an object's own properties, so nothing
/// comes from a prototype (including `Object.prototype`, which any code can
/// add to). Any prototype is fine otherwise, as are extra properties, frozen
/// objects and getters; a getter that throws is the input's fault.
#[test]
fn decoders_read_only_own_properties() {
    let examples = examples();
    let script = r#"
import * as trees from "./trees.mjs";
import * as shapes from "./shapes.mjs";
import assert from "node:assert/strict";

// Each module has its own error classes.
const inputError = (e) =>
  e instanceof shapes.StitchwortInputError || e instanceof trees.StitchwortInputError;
const refused = (f, pattern) => assert.throws(f, (e) => inputError(e) && pattern.test(e.message));

// An inherited tag, or field, isn't the object's own.
refused(() => trees.leaves(Object.create({ tag: "Leaf" })),
  /^arg0: its tag is inherited, not its own property$/);
const inheritsSide = Object.create({ side: 3n });
inheritsSide.tag = "Square";
refused(() => shapes.area(inheritsSide), /^arg0\.side: inherited, not the object's own property$/);
refused(() => shapes.area({ tag: "Square" }), /^arg0\.side: missing$/);
// So adding to `Object.prototype` can't fill in a missing field.
Object.prototype.side = 3n;
try {
  refused(() => shapes.area({ tag: "Square" }), /^arg0\.side: inherited, not the object's own property$/);
} finally {
  delete Object.prototype.side;
}
// Nor a class's getter.
class Square {
  get tag() { return "Square"; }
  side = 2n;
}
refused(() => shapes.area(new Square()), /^arg0: its tag is inherited, not its own property$/);

// Own properties are fine, whatever the prototype: none, or a class's.
const bare = Object.create(null);
bare.tag = "Square";
bare.side = 3n;
assert.equal(shapes.area(bare), 9n);
class Rect {
  constructor(width, height) {
    this.tag = "Rect";
    this.width = width;
    this.height = height;
  }
  area() { return this.width * this.height; }
}
assert.equal(shapes.area(new Rect(2n, 5n)), 10n);
// Extra properties are ignored, as TypeScript allows them.
assert.equal(shapes.area({ tag: "Square", side: 2n, colour: "red" }), 4n);
// Frozen objects and arrays are fine.
assert.deepEqual(shapes.areas(Object.freeze([Object.freeze({ tag: "Square", side: 2n })])), [4n]);

// A getter that throws refuses the input, with the error as the cause, even
// an error that would otherwise mean running out of resources.
const boom = new Error("boom");
assert.throws(() => shapes.area({ tag: "Square", get side() { throw boom; } }),
  (e) => e instanceof shapes.StitchwortInputError && e.message === "arg0.side: reading it threw Error: boom" && e.cause === boom);
assert.throws(() => shapes.area({ tag: "Square", get side() { throw new RangeError("deep"); } }),
  (e) => e instanceof shapes.StitchwortInputError && /^arg0\.side: reading it threw RangeError: deep$/.test(e.message));
refused(() => shapes.area({ get tag() { throw "a string"; } }), /^arg0: reading it threw a string$/);
// A getter whose answer changes is read once, even if its object is reached
// twice.
let reads = 0;
const shared = { tag: "Node", left: { tag: "Leaf" }, get right() { reads += 1; return reads === 1 ? { tag: "Leaf" } : 7; } };
assert.equal(trees.leaves({ tag: "Node", left: shared, right: shared }), 4n);
assert.equal(reads, 1);

// Arrays and objects aren't interchangeable, and an array can't have holes
// (which would be read from `Array.prototype`).
refused(() => shapes.area(["Square", 2n]), /^arg0: expected a Shape object, not an array$/);
refused(() => shapes.areas({ 0: { tag: "Square", side: 2n }, length: 1 }), /^arg0: expected an array$/);
refused(() => shapes.areas([{ tag: "Square", side: 2n }, , { tag: "Square", side: 2n }]), /^arg0\[1\]: a hole in the array$/);
Array.prototype[0] = { tag: "Square", side: 2n };
try {
  refused(() => shapes.areas(new Array(1)), /^arg0\[0\]: a hole in the array$/);
} finally {
  delete Array.prototype[0];
}
console.log("ok");
"#;
    run_script(
        "own",
        &[
            ("trees.mjs", example(&examples, "trees.sw")),
            ("shapes.mjs", example(&examples, "shapes.sw")),
        ],
        script,
    );
}

/// `Option T` at the boundary (D582): `T | undefined`, and an optional
/// property in a record's field; `null` is refused; a nested `Option` keeps
/// the tagged object.
#[test]
fn options_cross_the_boundary_as_undefined() {
    let examples = examples();
    let session = example(&examples, "options.sw");
    let dts = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds")
        .dts;
    for declaration in [
        "export type Profile = { readonly name: string; readonly nick?: string; readonly age?: bigint };",
        "export type Cap = { readonly cap?: number };",
        "export type Peek = { readonly items: readonly (bigint | undefined)[]; readonly extra?: readonly (bigint | undefined)[] };",
        "export type Both =\n  | { readonly tag: \"MkBoth\"; readonly left: bigint | undefined; readonly right: string };",
        "export declare function withNick(p: Profile, n: string | undefined): Profile;",
        "export declare function halve(arg0: bigint | undefined): bigint | undefined;",
        "export declare function wrap(x: bigint | undefined): Option<bigint> | undefined;",
        "export declare function unwrap(arg0: Option<bigint> | undefined): bigint | undefined;",
        "export declare function markAll(xs: readonly bigint[]): (bigint | undefined)[];",
        "export declare function capOf(c: Cap): number | undefined;",
    ] {
        assert!(dts.contains(declaration), "{declaration}\n{dts}");
    }
    let script = r#"
import * as m from "./options.mjs";
import assert from "node:assert/strict";

const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof m.StitchwortInputError && pattern.test(e.message));

// A record's field: a missing property and `undefined` are `None`.
assert.equal(m.nickname({ name: "Ada" }), "Ada");
assert.equal(m.nickname({ name: "Ada", nick: undefined }), "Ada");
assert.equal(m.nickname({ name: "Ada", nick: "Countess" }), "Countess");
// An empty string is a value, not `None`.
assert.equal(m.nickname({ name: "Ada", nick: "" }), "");
// `None` is no property (not one set to `undefined`); `Some` is the value.
const without = m.withNick({ name: "Ada", nick: "A", age: 36n }, undefined);
assert.deepEqual(Object.keys(without), ["name", "age"]);
assert.equal(Object.hasOwn(without, "nick"), false);
assert.deepEqual(without, { name: "Ada", age: 36n });
const withIt = m.withNick({ name: "Ada" }, "A");
assert.deepEqual(Object.keys(withIt), ["name", "nick"]);
assert.deepEqual(withIt, { name: "Ada", nick: "A" });
// `null` is refused, in a field and as an argument; so is an inherited field.
refused(() => m.nickname({ name: "Ada", nick: null }), /^p\.nick: expected a value or undefined, not null$/);
refused(() => m.withNick({ name: "Ada" }, null), /^n: expected a value or undefined, not null$/);
refused(() => m.nickname({ name: "Ada", nick: 5 }), /^p\.nick: expected a string$/);
refused(() => m.nickname({ name: "Ada", age: "x" }), /^p\.age: expected a non-negative bigint$/);
refused(() => m.nickname(Object.create({ name: "Ada" })), /^p\.name: inherited, not the object's own property$/);
refused(() => m.nickname({ name: "Ada", __proto__: { nick: "x" } }), /^p\.nick: inherited, not the object's own property$/);
// A required field is still required.
refused(() => m.nickname({ nick: "x" }), /^p\.name: missing$/);

// Argument and result.
assert.equal(m.halve(8n), 4n);
assert.equal(m.halve(undefined), undefined);
assert.equal(m.halve(0n), 0n);
refused(() => m.halve(null), /^arg0: expected a value or undefined, not null$/);
refused(() => m.halve(8), /^arg0: expected a non-negative bigint$/);
refused(() => m.halve({ tag: "Some", value: 8n }), /^arg0: expected a non-negative bigint$/);

// Nested: only the outer `Option` is `T | undefined`.
assert.equal(m.wrap(undefined).tag, "None");
assert.deepEqual(m.wrap(undefined), { tag: "None" });
assert.deepEqual(m.wrap(1n), { tag: "Some", value: 1n });
assert.deepEqual(m.wrap(undefined), { tag: "None" });
assert.deepEqual(m.unwrap(undefined), undefined);
assert.deepEqual(m.unwrap({ tag: "None" }), 0n);
assert.deepEqual(m.unwrap({ tag: "Some", value: 5n }), 5n);
refused(() => m.unwrap(null), /^arg0: expected a value or undefined, not null$/);
refused(() => m.unwrap({ tag: "Some" }), /^arg0\.value: missing$/);
refused(() => m.unwrap({ tag: "Some", value: null }), /^arg0\.value: expected a non-negative bigint$/);
refused(() => m.unwrap(5n), /^arg0: expected a Option object$/);

// A list's elements: `(T | undefined)[]`, with a hole in the array refused.
assert.deepEqual(m.keepSome([1n, undefined, 3n]), [1n, 3n]);
assert.deepEqual(m.markAll([1n, 2n, 3n]), [undefined, 2n, 3n]);
assert.equal(m.markAll([1n]).length, 1);
assert.equal(0 in m.markAll([1n]), true);
refused(() => m.keepSome([1n, null]), /^arg0\[1\]: expected a value or undefined, not null$/);
refused(() => m.keepSome([1n, "2"]), /^arg0\[1\]: expected a non-negative bigint$/);
refused(() => m.keepSome([1n, , 3n]), /^arg0\[1\]: a hole in the array$/);

// In a record, around lists and other options; round trip.
const peek = { items: [1n, undefined], extra: [undefined] };
assert.deepEqual(m.peek(peek), peek);
assert.deepEqual(m.peek({ items: [] }), { items: [] });
assert.equal(Object.hasOwn(m.peek({ items: [] }), "extra"), false);
assert.deepEqual(m.peek({ items: [], extra: [] }), { items: [], extra: [] });
refused(() => m.peek({ items: [], extra: [null] }), /^p\.extra\[0\]: expected a value or undefined, not null$/);

// A constructor's field is not a record's: present, as `T | undefined`.
assert.deepEqual(m.swapSides({ tag: "MkBoth", left: undefined, right: "xy" }), { tag: "MkBoth", left: 2n, right: "none" });
assert.deepEqual(m.swapSides({ tag: "MkBoth", left: 7n, right: "xy" }), { tag: "MkBoth", left: 2n, right: "7" });
refused(() => m.swapSides({ tag: "MkBoth", right: "x" }), /^arg0\.left: missing$/);
refused(() => m.swapSides({ tag: "MkBoth", left: null, right: "x" }), /^arg0\.left: expected a value or undefined, not null$/);

// A proof field about an optional one is checked after it's decoded.
assert.equal(m.required({ value: 3n }), 3n);
refused(() => m.required({}), /^r: proof field `ok` \(`Present value`\) doesn't hold$/);
refused(() => m.required({ value: undefined }), /^r: proof field `ok`/);

// `SafeNat` inside an optional property: a `number`.
assert.equal(m.capOf({ cap: 7 }), 7);
assert.equal(m.capOf({}), undefined);
assert.equal(m.capOf({ cap: 0 }), 0);
refused(() => m.capOf({ cap: 7n }), /^c\.cap: expected a number$/);
refused(() => m.capOf({ cap: 2 ** 53 }), /^c\.cap: expected a whole number from 0 to 9007199254740991$/);
refused(() => m.capOf({ cap: null }), /^c\.cap: expected a value or undefined, not null$/);
console.log("ok");
"#;
    run_script("options", &[("options.mjs", session)], script);
}

/// Records at the boundary (docs/proposals/records.md §11): plain objects
/// without a tag, keys in declared order, decoded as strictly as other data,
/// and proof fields re-established by their decision procedures.
#[test]
fn records_cross_the_boundary_strictly() {
    let examples = examples();
    let script = r#"
import * as r from "./records.mjs";
import assert from "node:assert/strict";

const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof r.StitchwortInputError && pattern.test(e.message));

// Out: a plain object, keys in declared order, no tag, proofs left out.
const ada = r.birthday({ name: "Ada", age: 36n });
assert.deepEqual(ada, { name: "Ada", age: 37n });
assert.deepEqual(Object.keys(r.birthday({ age: 1n, name: "x" })), ["name", "age"]);
assert.equal(Object.getPrototypeOf(ada), Object.prototype);
assert.deepEqual(r.sorted([1n, 2n]), { items: [1n, 2n] });
// Awkward keys: `tag` is an ordinary key; `__proto__` is still escaped.
const w = r.weird({ tag: "t", $__proto__: 1n, constructor: 2n, x$: 3n });
assert.deepEqual(Object.keys(w), ["tag", "$__proto__", "constructor", "x$"]);
assert.equal(w.tag, "t!");
assert.equal(Object.getPrototypeOf(w), Object.prototype);

// In: own properties only, every field present, extra ones ignored.
assert.equal(r.greet({ name: "Ada", age: 36n, email: "ada@example.com" }), "Hello, Ada");
refused(() => r.greet({ name: "Ada" }), /^p\.age: missing$/);
refused(() => r.greet(Object.create({ name: "Ada", age: 36n })), /^p\.name: inherited, not the object's own property$/);
refused(() => r.greet(["Ada", 36n]), /^p: expected a Person object, not an array$/);
refused(() => r.greet({ tag: "Person.mk", name: "Ada", age: -1n }), /^p\.age: /);
let reads = 0;
assert.equal(r.greet({ get name() { reads += 1; return "Ada"; }, age: 1n }), "Hello, Ada");
assert.equal(reads, 1);
refused(() => r.team({ lead: { name: "Ada" }, size: 1n }), /^t\.lead\.age: missing$/);

// Proof fields: checked after the fields they're about are decoded.
assert.deepEqual(r.smallest({ items: [1n, 4n] }), 1n);
refused(() => r.smallest({ items: [4n, 1n] }), /^arg0: proof field `ok` \(`IsSorted items`\) doesn't hold$/);
assert.equal(r.total({ items: [5n, 6n], size: 2n }), 2n);
refused(() => r.total({ items: [5n, 6n], size: 3n }), /^s: proof field `ok` \(`List.length items = size`\) doesn't hold$/);
// A proof passed in anyway is ignored, not trusted.
refused(() => r.total({ items: [], size: 1n, ok: true }), /^s: proof field `ok`/);
console.log("ok");
"#;
    run_script(
        "records",
        &[("records.mjs", example(&examples, "records.sw"))],
        script,
    );
}

/// DESIGN.md §12: an object reached by many paths is decoded once (at each
/// type), so input with much sharing, such as a DAG with 2^60 paths, decodes
/// quickly, and the value is the same as if nothing were shared.
#[test]
fn shared_input_is_decoded_once() {
    let source = "\
type Tree : Type =
  | Leaf
  | Node (left : Tree) (right : Tree)

def leftDepthOnto (n : Nat) : Tree -> Nat
  | Leaf     => n
  | Node l r => leftDepthOnto (Succ n) l

export def leftDepth (t : Tree) : Nat := leftDepthOnto 0 t

export def leaves : Tree -> Nat
  | Leaf     => 1
  | Node l r => leaves l + leaves r

export def echoTree (t : Tree) : Tree := t

type Both (a : Type) (b : Type) : Type =
  | MkBoth (first : a) (second : b)

export def echoBoth (p : Both (List Nat) (List Text)) : Both (List Nat) (List Text) := p
";
    let mut session = Session::new();
    session.load("shared.sw", source).expect("checks");
    let script = r#"
import * as m from "./shared.mjs";
import assert from "node:assert/strict";

// `d` levels, each node's children both the next level's one node: 2^d paths
// to the leaf, through d + 1 objects.
const dag = (d) => {
  let t = { tag: "Leaf" };
  for (let i = 0; i < d; i++) t = { tag: "Node", left: t, right: t };
  return t;
};
// Each node is read once: if not, this fails (quickly) rather than the
// next line taking forever.
let reads = 0;
let counted = { tag: "Leaf" };
for (let i = 0; i < 20; i++) {
  const child = counted;
  counted = { tag: "Node", get left() { reads++; return child; }, get right() { reads++; return child; } };
}
assert.equal(m.leftDepth(counted), 20n);
assert.equal(reads, 40);
const start = performance.now();
assert.equal(m.leftDepth(dag(60)), 60n);
assert.equal(m.leftDepth(dag(100000)), 100000n);
const elapsed = performance.now() - start;
assert.ok(elapsed < 5000, `took ${elapsed} ms`);

// The value is the full tree: Stitchwort code sees 2^16 leaves, and encoding
// it gives back a tree of fresh objects, none shared.
assert.equal(m.leaves(dag(16)), 65536n);
const out = m.echoTree(dag(12));
const objects = new Set();
let count = 0;
for (const stack = [out]; stack.length > 0; ) {
  const t = stack.pop();
  objects.add(t);
  count++;
  if (t.tag === "Node") stack.push(t.left, t.right);
  else assert.equal(t.tag, "Leaf");
}
assert.equal(count, 2 ** 13 - 1);
assert.equal(objects.size, count);

// What's remembered is per type: the same array is a `List Nat` in one place
// and a `List Text` in another, so it's refused in the second.
const shared = [1n];
assert.throws(() => m.echoBoth({ tag: "MkBoth", first: shared, second: shared }),
  (e) => e instanceof m.StitchwortInputError && e.message === "p.second[0]: expected a string");
const empty = [];
assert.deepEqual(m.echoBoth({ tag: "MkBoth", first: empty, second: empty }),
  { tag: "MkBoth", first: [], second: [] });

// Cycles are still refused.
const loop = { tag: "Node", left: { tag: "Leaf" }, right: null };
loop.right = { tag: "Node", left: loop, right: loop };
assert.throws(() => m.leftDepth(loop),
  (e) => e instanceof m.StitchwortInputError && e.message === "t.right.left: the input contains itself");
console.log("ok");
"#;
    run_script("shared", &[("shared.mjs", &session)], script);
}

/// A definition that failed to check has no body. The driver never extracts
/// a module with errors, but the generator refuses one rather than emitting
/// JS that calls a function that isn't there.
#[test]
fn the_generator_refuses_a_definition_without_a_body() {
    let source = "\
def helper (n : Nat) : Nat := True

export def f (n : Nat) : Nat := helper n
";
    let mut session = Session::new();
    assert!(session.load("broken.sw", source).is_err());
    let g = &session.elab.globals;
    let helper = (0..g.defs.len())
        .map(DefId)
        .find(|id| &*g.def(*id).name == "helper")
        .expect("`helper` is declared");
    assert!(g.def(helper).body().is_none());
    let e = stitchwort_js::generate(g, session.elab.limits)
        .err()
        .expect("generation is refused");
    assert_eq!(e.code, "E-EXPORT");
    let rendered = render(&session.sources, &e, false);
    assert!(
        rendered.contains("can't generate JavaScript for `"),
        "{rendered}"
    );
}

/// Runs a Node script, next to the generated modules it imports, and
/// requires it to print `ok`.
fn run_script(name: &str, modules: &[(&str, &Session)], script: &str) {
    let modules: Vec<(&str, String)> = modules
        .iter()
        .map(|(file, session)| {
            let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
                .expect("extraction succeeds");
            (*file, output.js)
        })
        .collect();
    run_script_on(name, &modules, script);
}

/// [`run_script`], with the modules' code given.
fn run_script_on(name: &str, modules: &[(&str, String)], script: &str) {
    let dir = std::env::temp_dir().join(format!("stitchwort-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    for (file, js) in modules {
        std::fs::write(dir.join(file), js).expect("write module");
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

fn example<'a>(examples: &'a [(String, String, Session)], name: &str) -> &'a Session {
    &examples
        .iter()
        .find(|(n, _, _)| n == name)
        .unwrap_or_else(|| panic!("{name}"))
        .2
}

/// The text-and-IO proposal's boundary cases: a `Text` decodes only from a
/// well-formed string, which it gives back unchanged; a `Char` from exactly
/// one scalar value. Nothing is repaired, truncated or normalised.
#[test]
fn text_and_chars_cross_the_boundary_strictly() {
    let examples = examples();
    let text = example(&examples, "text.sw");
    let script = r#"
import * as m from "./text.mjs";
import assert from "node:assert/strict";

const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof m.StitchwortInputError && pattern.test(e.message));

// A valid surrogate pair is one character, and comes back unchanged.
assert.equal(m.len("😀"), 1n);
assert.equal(m.echo("😀"), "\u{1F600}");
assert.deepEqual(m.chars("a\u{1F600}b"), ["a", "\u{1F600}", "b"]);

// Lone and malformed surrogates are refused, not repaired, wherever they are.
for (const [bad, index] of [
  ["\uD83D", 0],             // a lone high surrogate
  ["\uDE00", 0],             // a lone low surrogate
  ["ab\uD83D", 2],           // high, at the end
  ["a\uD83Db", 1],           // high, followed by something else
  ["\uDE00\uD83D", 0],       // a pair the wrong way round
  ["\uD83D😀", 0], // two highs, then a low
  ["\u{1F600}\uDE00", 2],    // a low after a valid pair
]) {
  const where = new RegExp(`lone surrogate \\(U\\+D[0-9A-F]{3}\\) at index ${index};`);
  refused(() => m.echo(bad), new RegExp(`^t: a ${where.source}`));
  refused(() => m.len(bad), where);
  refused(() => m.echoChar(bad), where);
}

// Nested inside a list, the prelude's `Option` and `Pair`, and a user's type,
// with the path to the problem.
refused(() => m.fromChars(["a", "\uD800"]), /^cs\[1\]: a lone surrogate/);
refused(() => m.joinOn(",", ["ok", "x\uDFFF"]), /^ts\[1\]: a lone surrogate \(U\+DFFF\) at index 1/);
refused(() => m.orEmpty("\uD800"), /^arg0: a lone surrogate/);
refused(() => m.firstOf({ tag: "MkPair", fst: "a", snd: "\uDBFF" }), /^p\.snd: a lone surrogate/);
refused(() => m.greet({ tag: "MkPerson", name: "\uDC00", initial: "x", tags: [] }), /^arg0\.name: a lone surrogate/);
refused(() => m.greet({ tag: "MkPerson", name: "x", initial: "xy", tags: [] }), /^arg0\.initial: expected exactly one character, but the string has 2$/);
refused(() => m.greet({ tag: "MkPerson", name: "x", initial: "x", tags: ["\uD800"] }), /^arg0\.tags\[0\]: a lone surrogate/);
assert.equal(m.greet({ tag: "MkPerson", name: "Zoë", initial: "\u{1F600}", tags: [] }), "Hello, Zoë (\u{1F600})");
assert.deepEqual(m.uncons("\u{1F600}x"), { tag: "MkPair", fst: "\u{1F600}", snd: "x" });

// A `Char` is exactly one scalar value: a supplementary one (`.length` 2) is
// accepted; a lone surrogate (one element of `[...s]`) isn't; nor is an
// empty string, or several scalars, even if they make one grapheme.
assert.equal(m.echoChar("\u{1F600}"), "\u{1F600}");
assert.equal(m.codeOf("\u{10FFFF}"), 0x10FFFFn);
assert.equal([..."\uD800"].length, 1);
refused(() => m.echoChar("\uD800"), /^c: a lone surrogate \(U\+D800\) at index 0;/);
refused(() => m.echoChar(""), /^c: expected exactly one character, but the string has 0$/);
refused(() => m.echoChar("ab"), /but the string has 2$/);
refused(() => m.echoChar("é"), /but the string has 2$/);
refused(() => m.echoChar("\u{1F600}\u{1F600}"), /but the string has 2$/);

// Only strings: not numbers, arrays, String objects or code points.
for (const notString of [97n, 97, ["a"], new String("a"), null, undefined, { tag: "MkText" }]) {
  refused(() => m.echo(notString), /^t: expected a string$/);
  refused(() => m.echoChar(notString), /^c: expected a string$/);
}

// NUL and noncharacters are ordinary characters: accepted, not truncated.
assert.equal(m.len("a\0b"), 3n);
assert.equal(m.echo("a\0b"), "a\0b");
assert.equal(m.echoChar("\0"), "\0");
assert.equal(m.codeOf("\0"), 0n);
const nonchars = "﷐﷯￾￿\u{1FFFE}\u{10FFFF}";
assert.equal(m.len(nonchars), 6n);
assert.equal(m.echo(nonchars), nonchars);
assert.deepEqual(m.chars(nonchars), [...nonchars]);
assert.equal(m.echo(""), "");
assert.equal(m.len(""), 0n);

// Round trips. A deterministic generator (mulberry32), so failures repeat.
let seed = 0x5717c4;
const random = () => {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = seed;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};
const unit = () => {
  const r = random();
  if (r < 0.3) return 0xd800 + Math.floor(random() * 0x800); // any surrogate
  if (r < 0.5) return Math.floor(random() * 0x80);
  return Math.floor(random() * 0x10000);
};

// encode (decode s) = s, as the same JS string, whenever decoding succeeds;
// and decoding succeeds exactly when the string is well-formed, as
// JavaScript's own `isWellFormed` says. Lengths count code points.
let wellFormed = 0;
for (let i = 0; i < 5000; i++) {
  const n = Math.floor(random() * 8);
  const s = String.fromCharCode(...Array.from({ length: n }, unit));
  if (s.isWellFormed()) {
    wellFormed++;
    assert.equal(m.echo(s), s);
    assert.equal(m.fromChars(m.chars(s)), s);
    assert.equal(m.len(s), BigInt([...s].length));
  } else {
    refused(() => m.echo(s), /lone surrogate/);
  }
}
assert.ok(wellFormed > 1000 && wellFormed < 4000, `${wellFormed} well-formed`);

// decode (encode t) = t: `fromChars` encodes a text built from characters,
// and `chars` decodes it again. Every scalar value from the edges of each
// range, and a sweep through all of them.
const codes = [0, 0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000, 0xfffd, 0xffff, 0x10000, 0x10ffff];
for (let c = 0; c <= 0x10ffff; c += 997) if (c < 0xd800 || c > 0xdfff) codes.push(c);
const all = codes.map((c) => String.fromCodePoint(c));
assert.deepEqual(m.chars(m.fromChars(all)), all);
for (const c of all) {
  assert.equal(m.echoChar(c), c);
  assert.equal(m.codeOf(c), BigInt(c.codePointAt(0)));
}
console.log("ok");
"#;
    run_script("text", &[("text.mjs", text)], script);
}

/// Long inputs in generated JS. The prelude's text operations are native, and
/// they and the bridges between a string and its `List Char` don't use JS
/// stack space proportional to a text's length, so they handle a million
/// characters through the whole export path: decoding, the operation, the
/// conversions, and encoding many short results, one long one, or a long
/// `List Char`. A function's tail calls to itself are loops, so they handle
/// any length too. Other recursion uses a JS stack frame per character (or
/// element, or level of nesting); running out of stack is a
/// `StitchwortResourceError`, after which the module still works.
#[test]
fn long_inputs_are_loops_or_resource_errors() {
    let examples = examples();
    let script = r#"
import * as loops from "./loops.mjs";
import * as text from "./text.mjs";
import * as trees from "./trees.mjs";
import assert from "node:assert/strict";

assert.equal(loops.sumTo(1000000n), 500000500000n);
assert.equal(loops.lastChar("ab".repeat(500000)), "b");
assert.equal(loops.countTail("a", "ab".repeat(500000)), 500000n);
assert.equal(text.reverse("ab".repeat(500000)), "ba".repeat(500000));

// Each native operation on a million characters.
const N = 1000000;
const long = "a".repeat(N);
const emoji = "\u{1F600}".repeat(N);
assert.equal(text.len(long), BigInt(N));
assert.equal(text.len(emoji), BigInt(N));
assert.equal(text.empty(long), false);
assert.equal(text.same(long, "a".repeat(N)), true);
assert.equal(text.same(long, "a".repeat(N - 1) + "b"), false);
assert.deepEqual(text.order(long, long + "a"), { tag: "Less" });
assert.deepEqual(text.order(emoji + "\u{E000}", emoji + "\u{10000}"), { tag: "Less" });
assert.equal(text.less(long, long), false);
assert.equal(text.join(long, long), long + long);
assert.equal(text.trim(" ".repeat(N) + "x" + " ".repeat(N)), "x");
assert.deepEqual(text.toNat("7".repeat(N)), BigInt("7".repeat(N)));
assert.equal(text.fromNat(10n ** 20000n).length, 20001);
assert.deepEqual(text.uncons(emoji), { tag: "MkPair", fst: "\u{1F600}", snd: emoji.slice(2) });
const codes = text.codes("a\u{1F600}".repeat(N / 2));
assert.equal(codes.length, N);
assert.equal(codes[1], 0x1f600n);
// One long result; many short ones, and joining them again.
assert.deepEqual(text.split(",", long), [long]);
const fields = text.split(",", "a,".repeat(N / 2));
assert.equal(fields.length, N / 2 + 1);
assert.ok(fields.every((f, i) => f === (i === N / 2 ? "" : "a")));
assert.equal(text.joinOn(",", fields), "a,".repeat(N / 2));
assert.equal(text.joinOn(",", Array(N).fill("")), ",".repeat(N - 1));
assert.equal(text.firstField(",", long + ","), long);
// Long `List Char`s, both ways, through user code's `MkText` too.
const cs = text.chars("a\u{1F600}".repeat(N / 2));
assert.equal(cs.length, N);
assert.ok(cs.every((c, i) => c === (i % 2 === 0 ? "a" : "\u{1F600}")));
assert.equal(text.fromChars(cs), "a\u{1F600}".repeat(N / 2));
assert.deepEqual(text.texts([cs]), ["a\u{1F600}".repeat(N / 2)]);
assert.deepEqual(text.trimmedHead(" ".repeat(N) + long), "a");
assert.equal(text.isText(long), true);

// User code that recurses once per character still runs out of stack.
const exhausted = (f, name) =>
  assert.throws(f, (e) =>
    e instanceof text.StitchwortResourceError || e instanceof trees.StitchwortResourceError
      ? new RegExp(`^${name}: ran out of resources`).test(e.message) && e.cause instanceof RangeError
      : false);
exhausted(() => text.countChar("a", long), "countChar");
let deep = { tag: "Leaf" };
for (let i = 0; i < 1000000; i++) deep = { tag: "Node", left: deep, right: { tag: "Leaf" } };
exhausted(() => trees.leaves(deep), "leaves");
// Input errors are still input errors.
assert.throws(() => text.len("\uD800"), text.StitchwortInputError);
assert.throws(() => text.len(long + "\uD800"), /lone surrogate \(U\+D800\) at index 1000000;/);

// Afterwards, everything still works.
assert.equal(text.countChar("a", "abc"), 1n);
assert.equal(trees.leaves({ tag: "Node", left: { tag: "Leaf" }, right: { tag: "Leaf" } }), 2n);
console.log("ok");
"#;
    run_script(
        "long",
        &[
            ("loops.mjs", example(&examples, "loops.sw")),
            ("text.mjs", example(&examples, "text.sw")),
            ("trees.mjs", example(&examples, "trees.sw")),
        ],
        script,
    );
}

/// Property-style differential tests of the text natives: every export of
/// `examples/extract/text.sw`, generated with native text operations and with
/// every operation compiled from its list definition, must give the same
/// result. On every short text over a small alphabet, every pair of shorter
/// ones, and thousands of random texts and pairs built from characters where
/// JavaScript's strings and Stitchwort's text disagree (including pairs that
/// share a long prefix, for comparison). The list-based code is itself
/// checked against the reference evaluator by the tests above.
#[test]
fn text_natives_agree_with_the_list_definitions() {
    let examples = examples();
    let g = &example(&examples, "text.sw").elab.globals;
    let module = |options| {
        stitchwort_js::generate_with(g, Limits::default(), options)
            .expect("extraction succeeds")
            .js
    };
    let script = r#"
import * as native from "./native.mjs";
import * as list from "./list.mjs";
import assert from "node:assert/strict";

const canon = (f) => {
  try {
    return JSON.stringify(f(), (_, x) => (typeof x === "bigint" ? `${x}n` : x));
  } catch (e) {
    return `threw ${e.name}`;
  }
};
let checked = 0;
const agree = (name, ...args) => {
  const n = canon(() => native[name](...args));
  const l = canon(() => list[name](...args));
  if (n !== l) assert.fail(`${name}(${args.map((a) => JSON.stringify(a)).join(", ")}): ${n} natively, ${l} by definition`);
  checked++;
};

// Where JS strings and Stitchwort text disagree, and ordinary characters.
const awkward = ["a", "Z", "0", "7", "9", " ", ",", "\t", "\n", "\v", "\f", "\r", "\0", "\u{E9}", "\u{301}",
  "\u{A0}", "\u{2028}", "\u{FEFF}", "\u{D7FF}", "\u{E000}", "\u{FDD0}", "\u{FFFE}", "\u{FFFF}", "\u{10000}",
  "\u{1F600}", "\u{1F601}", "\u{10FFFF}"];
// Every text up to four characters over these, and pairs up to two.
const small = ["a", ",", " ", "7", "\u{E000}", "\u{1F600}", "\u{1F601}"];
const upTo = (n) => {
  let all = [""], layer = [""];
  for (let k = 0; k < n; k++) {
    layer = layer.flatMap((t) => small.map((c) => t + c));
    all = all.concat(layer);
  }
  return all;
};
let seed = 0x7e47;
const random = () => {
  seed = (seed + 0x6d2b79f5) | 0;
  let t = seed;
  t = Math.imul(t ^ (t >>> 15), t | 1);
  t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
};
const pick = (xs) => xs[Math.floor(random() * xs.length)];
const randomText = (max) => Array.from({ length: Math.floor(random() * max) }, () => pick(awkward)).join("");
// A copy with one character changed, added or removed, at a random place.
const mutate = (t) => {
  const cs = [...t];
  const i = Math.floor(random() * (cs.length + 1));
  const r = random();
  if (r < 0.4 && i < cs.length) cs[i] = pick(awkward);
  else if (r < 0.7) cs.splice(i, 0, pick(awkward));
  else cs.splice(i, 1);
  return cs.join("");
};

const texts = upTo(4);
for (let i = 0; i < 3000; i++) texts.push(randomText(24));
const pairs = upTo(2).flatMap((a) => upTo(2).map((b) => [a, b]));
for (let i = 0; i < 3000; i++) {
  const a = randomText(24);
  pairs.push([a, random() < 0.8 ? mutate(a) : randomText(24)]);
}

for (const t of texts) {
  for (const name of ["len", "chars", "echo", "trim", "toNat", "uncons", "reverse", "codes", "empty", "isText", "trimmedHead"]) {
    agree(name, t);
  }
  agree("fromChars", [...t]);
  for (const c of [",", " ", "\u{1F600}", "7", [...t][0] ?? "a"]) {
    agree("split", c, t);
    agree("countChar", c, t);
    agree("firstField", c, t);
  }
}
for (const [a, b] of pairs) {
  for (const name of ["same", "order", "less", "join"]) agree(name, a, b);
  agree("joinOn", ",", [a, b]);
  agree("joinOn", "\u{1F600}", [a, "", b]);
  agree("lengths", [a, b]);
  agree("prefixAll", [a, b]);
  agree("texts", [[...a], [...b]]);
  agree("split", [...b][0] ?? ",", a);
}
for (let i = 0; i < 300; i++) {
  agree("joinOn", pick(awkward), Array.from({ length: Math.floor(random() * 6) }, () => randomText(6)));
  agree("toNat", Array.from({ length: Math.floor(random() * 30) }, () => pick(["0", "1", "7", "9"])).join("") + (random() < 0.2 ? pick(awkward) : ""));
}
for (const n of [0n, 1n, 9n, 10n, 99n, 100n, 2n ** 64n, 10n ** 40n - 1n, 10n ** 40n]) agree("fromNat", n);
for (const s of ["", "0", "007", " 12", "+5", "12abc", "0x10", "1e3", "\u{661}\u{662}", "12\n", "1_000", "18446744073709551616"]) {
  agree("toNat", s);
}
assert.ok(checked > 100000, `${checked} checked`);
console.log("ok");
"#;
    run_script_on(
        "natives",
        &[
            ("native.mjs", module(Options::default())),
            ("list.mjs", module(LIST_TEXT)),
        ],
        script,
    );
}

/// The two ways of generating code differ exactly where `Text` is involved.
/// With native text, a constructor-only match on `MkText` converts nothing,
/// and the list-based module has no string helpers, except for building a
/// text literal's list of characters (a compact list in the checked term).
#[test]
fn native_text_is_only_used_when_asked_for() {
    let examples = examples();
    let g = &example(&examples, "text.sw").elab.globals;
    let native = stitchwort_js::generate(g, Limits::default()).expect("extraction succeeds");
    let list =
        stitchwort_js::generate_with(g, Limits::default(), LIST_TEXT).expect("extraction succeeds");
    assert!(
        native
            .js
            .contains("const $Main$disText = (v0) => {\n  return { tag: \"True\" };\n};")
    );
    assert!(native.js.contains("const $Std$dText$dlength = (t) => {"));
    assert!(!list.js.contains("textOfChars"));
    let uses: Vec<&str> = list.js.split("charsOfText(").skip(1).collect();
    assert!(!uses.is_empty());
    assert!(
        uses.iter().all(|rest| rest.starts_with('"')),
        "the list-based module converts only literals"
    );
    assert!(list.js.contains("tag: \"MkText\", chars: charsOfText(\""));
    // The declarations don't depend on the representation.
    assert_eq!(native.dts, list.dts);
}

/// Decoding and encoding keep their own stack, so deeply nested values cross
/// the boundary both ways: a user's list of a million elements, a tree a
/// million deep, and a list type with a
/// parameter. Errors deep inside still say where they are, briefly.
#[test]
fn deep_values_cross_the_boundary() {
    let examples = examples();
    let script = r#"
import * as m from "./deep.mjs";
import assert from "node:assert/strict";

const N = 1000000;
const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof m.StitchwortInputError && pattern.test(e.message));

// A user's list, a million long: decoded only, decoded and encoded, and
// built by Stitchwort code and encoded.
const chainOf = (n, head = (i) => BigInt(i)) => {
  let c = { tag: "End" };
  for (let i = n - 1; i >= 0; i--) c = { tag: "More", head: head(i), tail: c };
  return c;
};
const checkChain = (c, n, head = (i) => BigInt(i)) => {
  let i = 0;
  for (; c.tag === "More"; c = c.tail, i++) {
    if (c.head !== head(i) || Object.keys(c).length !== 3) assert.fail(`element ${i}`);
  }
  assert.equal(c.tag, "End");
  assert.equal(i, n);
};
const chain = chainOf(N);
assert.equal(m.count(chain), BigInt(N));
checkChain(m.echo(chain), N);
checkChain(m.flip(chain), N, (i) => BigInt(N - 1 - i));
checkChain(m.build(BigInt(N)), N);

// The path to a problem deep inside is summarised.
refused(() => m.count(chainOf(N, (i) => (i === N - 1 ? -1n : 0n))),
  /^c\(\.tail ×999999\)\.head: expected a non-negative bigint$/);
refused(() => m.count(chainOf(5, (i) => (i === 4 ? -1n : 0n))),
  /^c\.tail\.tail\.tail\.tail\.head: expected a non-negative bigint$/);
const loop = chainOf(N);
let last = loop;
while (last.tail.tag === "More") last = last.tail;
last.tail = loop;
refused(() => m.count(loop), /^c\(\.tail ×1000000\): the input contains itself$/);

// A tree a million deep down its left side, both ways.
let tree = { tag: "Leaf" };
for (let i = 0; i < N; i++) tree = { tag: "Node", left: tree, right: { tag: "Leaf" } };
const checkSpine = (t, n) => {
  let depth = 0;
  for (; t.tag === "Node"; t = t.left, depth++) {
    if (t.right.tag !== "Leaf") assert.fail(`depth ${depth}`);
  }
  assert.equal(depth, n);
};
checkSpine(m.echoTree(tree), N);
checkSpine(m.spine(BigInt(N)), N);

// A zigzag path repeats a two-step cycle, which is folded.
let zigzag = { tag: "Node", left: { tag: "Leaf" }, right: 7 };
for (let i = 0; i < N; i++) {
  zigzag = i % 2 === 0
    ? { tag: "Node", left: zigzag, right: { tag: "Leaf" } }
    : { tag: "Node", left: { tag: "Leaf" }, right: zigzag };
}
refused(() => m.echoTree(zigzag),
  /^t\(\.right\.left ×500000\)\.right: expected a Tree object$/);

// A list type with a parameter.
let seq = { tag: "Stop" };
for (let i = 0; i < N; i++) seq = { tag: "Step", item: "x", rest: seq };
const checkSeq = (s, n) => {
  let i = 0;
  for (; s.tag === "Step"; s = s.rest, i++) if (s.item !== "x") assert.fail(`item ${i}`);
  assert.equal(i, n);
};
checkSeq(m.echoSeq(seq), N);
checkSeq(m.steps(BigInt(N)), N);
refused(() => m.echoSeq({ tag: "Step", item: "x", rest: { tag: "Step", item: "\uD800", rest: { tag: "Stop" } } }),
  /^s\.rest\.item: a lone surrogate \(U\+D800\) at index 0;/);
console.log("ok");
"#;
    run_script(
        "deep",
        &[("deep.mjs", example(&examples, "deep.sw"))],
        script,
    );
}

/// Data types defined together cross the boundary as deep as plain ones:
/// a tree a million deep, through its forest, decoded and encoded, and built
/// by Stitchwort code. Recursion over it is a resource error, not a crash.
/// Traversing the types (which refer to each other) terminating, and
/// traversing a deep value without overflowing, are separate properties
/// (docs/proposals/mutual-recursion.md §8.6).
#[test]
fn deep_mutual_values_cross_the_boundary() {
    let examples = examples();
    let script = r#"
import * as m from "./mutual-data.mjs";
import assert from "node:assert/strict";

const N = 1000000;
const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof m.StitchwortInputError && pattern.test(e.message));

// A tree a million deep: each node's only child is the next one down.
let tree = { tag: "Node", label: 0n, kids: { tag: "FNil" } };
for (let i = 1; i <= N; i++) {
  tree = { tag: "Node", label: BigInt(i), kids: { tag: "FCons", first: tree, rest: { tag: "FNil" } } };
}
// Labels count down to 0 at the bottom (`deep`'s count up, so aren't
// checked).
const checkDeep = (t, n, labelled = true) => {
  let depth = 0;
  while (t.kids.tag === "FCons") {
    if (t.kids.rest.tag !== "FNil" || (labelled && t.label !== BigInt(n - depth))) {
      assert.fail(`depth ${depth}`);
    }
    t = t.kids.first;
    depth++;
  }
  assert.equal(depth, n);
};
checkDeep(m.echoTree(tree), N);
checkDeep(m.deep(BigInt(N)), N, false);
// The forest it's in, too.
const forest = { tag: "FCons", first: tree, rest: { tag: "FNil" } };
const back = m.echoForest(forest);
checkDeep(back.first, N);

// A mistake at the bottom is found, and where it is is summarised.
let bad = { tag: "Node", label: -1n, kids: { tag: "FNil" } };
for (let i = 0; i < N; i++) bad = { tag: "Node", label: 0n, kids: { tag: "FCons", first: bad, rest: { tag: "FNil" } } };
refused(() => m.echoTree(bad),
  /^t\(\.kids\.first ×1000000\)\.label: expected a non-negative bigint$/);
// An alternating path folds its two-step cycle.
let alternating = { tag: "Node", label: -1n, kids: { tag: "FNil" } };
for (let i = 0; i < 6; i++) alternating = { tag: "Node", label: 0n, kids: { tag: "FCons", first: alternating, rest: { tag: "FNil" } } };
refused(() => m.echoTree(alternating),
  /^t\(\.kids\.first ×6\)\.label: expected a non-negative bigint$/);
// A tree that contains itself, through its forest.
const loop = { tag: "Node", label: 0n, kids: { tag: "FNil" } };
loop.kids = { tag: "FCons", first: loop, rest: { tag: "FNil" } };
refused(() => m.size(loop), /contains itself/);

// `size` and `sizeForest` call each other, so a deep tree runs out of
// stack: a resource error, after which the module still works.
assert.throws(() => m.size(tree), (e) => e instanceof m.StitchwortResourceError);
assert.equal(m.size({ tag: "Node", label: 0n, kids: { tag: "FNil" } }), 1n);

// With a parameter: a rose tree of texts, a million deep.
let rose = { tag: "Bloom", value: "x", kids: { tag: "NoRoses" } };
for (let i = 0; i < N; i++) {
  rose = { tag: "Bloom", value: "x", kids: { tag: "MoreRoses", first: rose, rest: { tag: "NoRoses" } } };
}
let r = m.echoRose(rose);
let depth = 0;
for (; r.kids.tag === "MoreRoses"; r = r.kids.first) depth++;
assert.equal(depth, N);
refused(() => m.echoRose({ tag: "Bloom", value: 1n, kids: { tag: "NoRoses" } }), /^r\.value: /);
console.log("ok");
"#;
    run_script(
        "mutual-data",
        &[("mutual-data.mjs", example(&examples, "mutual-data.sw"))],
        script,
    );
}

/// A type without constructors has no values: its declaration is `never`,
/// and the decoder says so.
#[test]
fn a_type_without_values_refuses_everything() {
    let source = "type Never : Type\n\nexport def fromNever (n : Never) : Nat := 0\n";
    let mut session = Session::new();
    session.load("never.sw", source).expect("checks");
    let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds");
    assert!(
        output.dts.contains("export type Never = never;\n"),
        "{}",
        output.dts
    );
    let script = r#"
import * as m from "./never.mjs";
import assert from "node:assert/strict";
assert.throws(() => m.fromNever({ tag: "Never" }), /^StitchwortInputError: n: unknown tag "Never"; expected nothing: Never has no values$/);
console.log("ok");
"#;
    run_script("never", &[("never.mjs", &session)], script);
}

/// Property-style: data types whose fields, constructors and parameters are
/// named from a pool of awkward names (`tag`, `__proto__`, primes, the
/// runtime's own names, JS globals and reserved words), exported under such
/// names too. On random values, each export must give back exactly what it
/// was given; every object must have its own key for each of its fields (so
/// no two fields share one, and none sets the prototype); and the TypeScript
/// declarations must accept exactly those objects.
#[test]
fn awkward_names_never_collide() {
    const FIELDS: &[&str] = &[
        "tag",
        "__proto__",
        "constructor",
        "toString",
        "valueOf",
        "hasOwnProperty",
        "prototype",
        "length",
        "x",
        "x'",
        "x''",
        "tag'",
        "tag''",
        "_tag",
        "tag_",
        "__proto__'",
        "path",
        "inside",
        "v0",
        "v1",
        "s0",
        "arg0",
        "arg1",
        "e",
        "m",
        "n",
        "undefined",
        "eval",
        "arguments",
        "class",
        "new",
        "delete",
        "default",
        "this",
        "enter",
        "decode",
        "encode",
        "data",
        "list",
        "close",
        "refuse",
        "value",
        "kind",
        "open",
        "info",
        "args",
        "fields",
        "out",
        "root",
        "head",
        "tail",
        "chars",
        "code",
    ];
    // Types and definitions share a namespace, so these are disjoint.
    const TYPES: &[&str] = &[
        "Tag", "Map", "Error", "Array", "Symbol", "Box'", "Box''", "Tag'", "LEAF", "DATA", "PARAM",
        "Promise", "Function",
    ];
    const EXPORTS: &[&str] = &[
        "enter",
        "decode",
        "encode",
        "data",
        "list",
        "close",
        "refuse",
        "describe",
        "pathText",
        "scalars",
        "outOfResources",
        "define",
        "datatype",
        "leaf",
        "param",
        "encodeChar",
        "wellFormed",
        "listOf",
        "scalarEndingAt",
        "charsOfText",
        "textOfChars",
        "Set",
        "BigInt",
        "String",
        "JSON",
        "Object",
        "Number",
        "RangeError",
        "Refusal",
        "NONE",
        "NAT",
        "TEXT",
        "LIST",
        "globalThis",
        "NaN",
        "Infinity",
    ];
    const CTORS: &[&str] = &["Tag", "Object", "X'", "X''", "Proto", "C"];
    const ROUNDS: usize = 4;
    const TYPES_PER_ROUND: usize = 8;
    const CASES_PER_EXPORT: usize = 10;
    const RECORDS_PER_ROUND: usize = 3;

    let mut rng = Rng(0x5eed_0fa7_4a3e);
    let pick = |rng: &mut Rng, pool: &[&'static str], n: usize| -> Vec<&'static str> {
        let mut pool = pool.to_vec();
        (0..n.min(pool.len()))
            .map(|_| pool.swap_remove(rng.below(pool.len())))
            .collect()
    };
    for round in 0..ROUNDS {
        let types = pick(&mut rng, TYPES, TYPES_PER_ROUND);
        let exports = pick(&mut rng, EXPORTS, TYPES_PER_ROUND);
        let mut source = String::new();
        // Each constructor's number of fields, which its objects' own keys
        // must match (one more, for the tag).
        let mut counts = Vec::new();
        for (k, (ty, export)) in types.iter().zip(&exports).enumerate() {
            let mut field_types = vec!["Nat", "Text", "Bool", "Char", "List Nat", "Option Text"];
            field_types.extend(&types[..k]);
            let mut ctors = Vec::new();
            let n = 1 + rng.below(3);
            for (c, ctor) in pick(&mut rng, CTORS, n).into_iter().enumerate() {
                let ctor = format!("{ctor}{round}{k}");
                let n = rng.below(6);
                let fields = pick(&mut rng, FIELDS, n);
                let fields: Vec<String> = fields
                    .iter()
                    .map(|f| {
                        // The first constructor isn't recursive, so values end.
                        let ty = if c > 0 && rng.below(3) == 0 {
                            ty
                        } else {
                            field_types[rng.below(field_types.len())]
                        };
                        format!("({f} : {ty})")
                    })
                    .collect();
                counts.push(format!(
                    "{}: {}",
                    js_string_literal(&ctor),
                    fields.len() + 1
                ));
                ctors.push((ctor, fields));
            }
            let _ = writeln!(source, "type {ty} : Type =");
            for (ctor, fields) in &ctors {
                let _ = writeln!(source, "  | {ctor} {}", fields.join(" "));
            }
            let param = FIELDS[rng.below(FIELDS.len())];
            let _ = writeln!(source, "\nexport def {export} : ({param} : {ty}) -> {ty}");
            for (ctor, fields) in &ctors {
                let vars: Vec<String> = (0..fields.len()).map(|i| format!("y{i}")).collect();
                let vars = vars.join(" ");
                let _ = writeln!(source, "  | {ctor} {vars} => {ctor} {vars}");
            }
            source.push('\n');
        }
        // Records (docs/proposals/records.md §11.2): no tag, so a field `tag`
        // is the key `tag`. Each is exported through an update that reads a
        // field with `.`.
        for k in 0..RECORDS_PER_ROUND {
            let mut field_types = vec!["Nat", "Text", "Bool", "Char", "List Nat", "Option Text"];
            field_types.extend(&types);
            let count = 1 + rng.below(6);
            let fields = pick(&mut rng, FIELDS, count);
            let declared: Vec<String> = fields
                .iter()
                .map(|f| format!("{f} : {}", field_types[rng.below(field_types.len())]))
                .collect();
            let _ = writeln!(source, "type Rec{round}{k} = {{ {} }}", declared.join(", "));
            let f = fields[rng.below(fields.len())];
            let _ = writeln!(
                source,
                "\nexport def record{round}{k} (r : Rec{round}{k}) : Rec{round}{k} := {{ r | {f} = r.{f} }}\n"
            );
        }

        let name = format!("awkward-{round}.sw");
        let mut session = Session::new();
        if let Err(diagnostics) = session.load(&name, &source) {
            let rendered: String = diagnostics
                .iter()
                .map(|d| render(&session.sources, d, false))
                .collect();
            panic!("{name} doesn't check:\n{rendered}\n{source}");
        }
        let g = &session.elab.globals;
        let output = stitchwort_js::generate(g, Limits::default()).expect("extraction succeeds");
        let mut script = format!(
            "import * as m from \"./module.mjs\";\n\
             import assert from \"node:assert/strict\";\n\
             const counts = {{ {} }};\n\
             const check = (v) => {{\n\
               if (typeof v !== \"object\" || v === null) return;\n\
               if (Array.isArray(v)) {{ v.forEach(check); return; }}\n\
               assert.equal(Object.getPrototypeOf(v), Object.prototype);\n\
               if (Object.hasOwn(counts, v.tag)) assert.equal(Object.keys(v).length, counts[v.tag], JSON.stringify(Object.keys(v)));\n\
               Object.values(v).forEach(check);\n\
             }};\n",
            counts.join(", ")
        );
        let mut typescript = String::from("import * as m from \"./module\";\n");
        for id in (0..g.defs.len()).map(DefId).filter(|id| g.def(*id).export) {
            let sig = exportable(g, id).expect("exports check");
            let (_, b) = &sig.params[0];
            for _ in 0..CASES_PER_EXPORT {
                let value = random_value(g, b, &mut rng, 3);
                let literal = boundary_literal(g, b, &value).expect("argument encodes");
                let _ = writeln!(
                    script,
                    "{{ const input = {literal}; check(input); const r = m.{}({literal}); check(r); assert.deepEqual(r, input); assert.deepEqual(Object.keys(r), Object.keys(input)); }}",
                    sig.name
                );
                let _ = writeln!(typescript, "m.{}({literal});", sig.name);
            }
        }
        script.push_str("console.log(\"ok\");\n");

        let dir =
            std::env::temp_dir().join(format!("stitchwort-awkward-{}-{round}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("create temp dir");
        std::fs::write(dir.join("module.mjs"), &output.js).expect("write module");
        std::fs::write(dir.join("module.d.ts"), &output.dts).expect("write declarations");
        std::fs::write(dir.join("test.mjs"), &script).expect("write script");
        std::fs::write(dir.join("check.ts"), &typescript).expect("write TypeScript");
        let result = Command::new("node")
            .arg("test.mjs")
            .current_dir(&dir)
            .output()
            .expect("run `node`");
        assert!(
            result.status.success() && String::from_utf8_lossy(&result.stdout).trim() == "ok",
            "{name}:\n{}\n--- source ---\n{source}",
            String::from_utf8_lossy(&result.stderr)
        );
        let result = Command::new("tsc")
            .args(["--noEmit", "--strict", "--target", "es2020", "check.ts"])
            .current_dir(&dir)
            .output()
            .expect("run `tsc`");
        assert!(
            result.status.success(),
            "{name}: the declarations don't accept the module's values:\n{}{}\n--- module.d.ts ---\n{}",
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr),
            output.dts
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}

/// Each text native is used only for the exact definition it was written for
/// (by content hash), and every one of them applies to the prelude. If this
/// fails after a change to the prelude, check each native listed against the
/// changed definition, then update its hash in `TEXT_NATIVES`.
#[test]
fn text_natives_are_bound_to_the_prelude() {
    let session = Session::eager();
    let bindings = stitchwort_js::bind_text_natives(&session.elab.globals).expect("hashes");
    let unbound: Vec<String> = bindings
        .iter()
        .filter(|b| !b.bound)
        .map(|b| format!("{}: {:?}", b.name, b.hash))
        .collect();
    assert!(
        unbound.is_empty(),
        "text natives not bound to the prelude's definitions:\n{}",
        unbound.join("\n")
    );
}

/// The `bigint` representation and every integer native apply to the
/// prelude's `Int` and its definitions. If the prelude changes, this prints
/// the new hashes: check the representation or the native against the
/// changed declaration before updating them in `crates/js`.
#[test]
fn int_is_bound_to_the_prelude() {
    let session = Session::eager();
    let binding = stitchwort_js::bind_int(&session.elab.globals).expect("hashes");
    let mut unbound: Vec<String> = binding
        .natives
        .iter()
        .filter(|b| !b.bound)
        .map(|b| format!("{}: {:?}", b.name, b.hash))
        .collect();
    if !binding.bound {
        unbound.insert(0, format!("the data type `Int`: {:?}", binding.hash));
    }
    assert!(
        unbound.is_empty(),
        "integer representation or natives not bound to the prelude's declarations:\n{}",
        unbound.join("\n")
    );
}

/// The `bigint` representation of `Nat` and the string representation of
/// `Text` apply to the prelude's declarations. If the prelude changes, this
/// prints the new hashes: re-check the JS representation against the changed
/// declarations before updating `NAT_DATA_HASH` or `TEXT_DATA_HASH` in
/// `crates/js`.
#[test]
fn nat_and_text_are_bound_to_the_prelude() {
    let session = Session::new();
    let g = &session.elab.globals;
    let mut unbound = Vec::new();
    for (name, builtin, expected) in [
        ("Nat", Builtin::Nat, stitchwort_js::NAT_DATA_HASH),
        ("Text", Builtin::Text, stitchwort_js::TEXT_DATA_HASH),
    ] {
        let d = g
            .registry
            .data(builtin)
            .unwrap_or_else(|| panic!("the prelude declares {name}"));
        let hash = data_hash(g, d).expect("hashes").expect("checked").hex();
        if hash != expected {
            unbound.push(format!("the data type `{name}`: {hash:?}"));
        }
    }
    assert!(
        unbound.is_empty(),
        "`Nat` or `Text` representation not bound to the prelude's declarations; \
         re-check the JS representation and update its hash in `crates/js`:\n{}",
        unbound.join("\n")
    );
}

/// The `number` codec of `SafeNat` and `SafeInt` is written for the library's
/// declarations (std/Int/Safe.sw), bounds included. If they change, this
/// prints the new hashes: re-check the codec in `crates/js` (`safe_codecs`)
/// against the changed declarations before updating `SAFE_NAT_HASH` or
/// `SAFE_INT_HASH` in `crates/rt`.
#[test]
fn safe_numbers_are_bound_to_the_library() {
    let examples = examples();
    let session = example(&examples, "safe-numbers.sw");
    let g = &session.elab.globals;
    let mut unbound = Vec::new();
    for (name, builtin, expected) in [
        ("SafeNat", Builtin::SafeNat, stitchwort_js::SAFE_NAT_HASH),
        ("SafeInt", Builtin::SafeInt, stitchwort_js::SAFE_INT_HASH),
    ] {
        let d = g
            .registry
            .data(builtin)
            .unwrap_or_else(|| panic!("the library declares {name}"));
        let hash = data_hash(g, d).expect("hashes").expect("checked").hex();
        if hash != expected {
            unbound.push(format!("the data type `{name}`: {hash:?}"));
        }
    }
    assert!(
        unbound.is_empty(),
        "`SafeNat` or `SafeInt` codec not bound to the library's declarations; \
         re-check the JS codec and update its hash in `crates/rt`:\n{}",
        unbound.join("\n")
    );
}

/// Definitions that call each other (docs/proposals/mutual-recursion.md
/// §8.6). Only a definition's tail calls to itself are loops, so `isEven` on
/// a large number uses a stack frame per step and runs out: a resource
/// error, never a wrong answer, after which the module still works.
#[test]
fn mutual_tail_calls_run_out_of_stack_cleanly() {
    let examples = examples();
    let script = r#"
import * as mutual from "./mutual.mjs";
import assert from "node:assert/strict";

assert.equal(mutual.isEven(1000n), true);
assert.throws(
  () => mutual.isEven(10000000n),
  (e) =>
    e instanceof mutual.StitchwortResourceError &&
    /^isEven: ran out of resources/.test(e.message) &&
    e.cause instanceof RangeError,
);
assert.equal(mutual.isOdd(7n), true);
console.log("ok");
"#;
    run_script(
        "mutual",
        &[("mutual.mjs", example(&examples, "mutual.sw"))],
        script,
    );
}

/// Deep recursion through `match` (docs/proposals/syntax-conveniences.md
/// section 4). A `match` that is a whole right-hand side is part of the case
/// tree, so its tail call to the owner is a loop (`countTail`). A lifted
/// `match` (here because the equation is named, `countNamed`) in tail
/// position is a pair of mutual tail calls, which aren't loops: it runs out
/// of stack, cleanly, as a resource error.
///
/// The second half documents a limitation: update it when mutual tail calls
/// become loops (TODO.md, "Mutual tail calls aren't loops").
#[test]
fn deep_recursion_through_match() {
    let examples = examples();
    let script = r#"
import * as m from "./match.mjs";
import assert from "node:assert/strict";

assert.equal(m.countTail(1000000n), 0n);
assert.equal(m.countNamed(1000n), 0n);
assert.throws(
  () => m.countNamed(1000000n),
  (e) =>
    e instanceof m.StitchwortResourceError &&
    /^countNamed: ran out of resources/.test(e.message) &&
    e.cause instanceof RangeError,
);
// Afterwards, everything still works.
assert.equal(m.count(10n), 11n);
console.log("ok");
"#;
    run_script(
        "match",
        &[("match.mjs", example(&examples, "match.sw"))],
        script,
    );
}

/// A member of a group with no runtime parameters (only an erased type
/// parameter) is a thunk, never a value computed when the module loads:
/// `k` calls `f`, which is defined after it. No source program reaches this
/// (any cycle through such a member loses every argument's size, so it's
/// refused), so the group, with no cycle at all, is built in the kernel
/// directly: a group bigger than necessary is still admitted.
#[test]
fn a_group_member_with_only_erased_parameters_is_a_thunk() {
    use std::rc::Rc;
    use stitchwort_core::check::{declare_def, define_def, define_group};
    use stitchwort_core::{Icit, Sort};

    let mut session = Session::new();
    session
        .load("empty.sw", "")
        .expect("an empty module checks");
    let g = &mut session.elab.globals;
    let nat = g.find_data("Nat").expect("Nat");
    let add = DefId(
        g.defs
            .iter()
            .position(|d| &*d.name == "Nat.add")
            .expect("Nat.add"),
    );
    let nat_ty = || Rc::new(Term::Data(nat, Vec::new()));
    let span = g.def(add).span;
    let num = |n: u32| Term::Nat(Rc::new(BigUint::from(n)));
    let app = |f: Term, a: Term| Term::App(Rc::new(f), Rc::new(a), Icit::Explicit);
    // k : [a : Type] -> Nat;  k = f 3
    let k_ty = Term::Pi(
        "a".into(),
        Icit::Implicit,
        Rc::new(Term::Sort(Sort::Type(0))),
        nat_ty(),
    );
    let k = declare_def(g, &"k".into(), &k_ty, false, false, span).unwrap();
    // f : Nat -> Nat;  f n = n + 1
    let f_ty = Term::Pi("n".into(), Icit::Explicit, nat_ty(), nat_ty());
    let f = declare_def(g, &"f".into(), &f_ty, false, false, span).unwrap();
    let k_body = Term::Lam(
        "a".into(),
        Icit::Implicit,
        Rc::new(app(Term::Def(f), num(3))),
    );
    let f_body = Term::Lam(
        "n".into(),
        Icit::Explicit,
        Rc::new(app(app(Term::Def(add), Term::Var(0)), num(1))),
    );
    define_group(g, &[(k, k_body), (f, f_body)]).unwrap();
    // export useK : Nat -> Nat;  useK n = n + k [Nat]
    let use_k = declare_def(g, &"useK".into(), &f_ty, false, true, span).unwrap();
    let k_nat = Term::App(
        Rc::new(Term::Def(k)),
        Rc::new(Term::Data(nat, Vec::new())),
        Icit::Implicit,
    );
    let use_k_body = Term::Lam(
        "n".into(),
        Icit::Explicit,
        Rc::new(app(app(Term::Def(add), Term::Var(0)), k_nat)),
    );
    define_def(g, use_k, &use_k_body).unwrap();

    let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds");
    assert!(
        output.js.contains("const $Main$dk = () => "),
        "{}",
        output.js
    );
    let script = r#"
import { useK } from "./erased.mjs";
import assert from "node:assert/strict";
assert.equal(useK(1n), 5n);
console.log("ok");
"#;
    run_script_on("erased", &[("erased.mjs", output.js)], script);
}

/// A text literal is one compact list in the checked term, however long, and
/// extracts to one JS string literal, or (with list-based text) to that
/// string turned into a cons list in a loop. Both give the same results, and
/// user code's match on `MkText` sees the characters (compact text, stage 2).
#[test]
fn long_literals_extract_as_strings() {
    let text: String = (0..300_000)
        .map(|i| match i % 6 {
            0 => '\u{1F600}',
            1 => '"',
            2 => '\\',
            3 => '\n',
            _ => 'a',
        })
        .collect();
    let mut literal = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => literal.push_str("\\\""),
            '\\' => literal.push_str("\\\\"),
            '\n' => literal.push_str("\\n"),
            '\u{1F600}' => literal.push_str("\\u{1F600}"),
            c => literal.push(c),
        }
    }
    literal.push('"');
    let source = format!(
        "import Std (Text)\n\n\
         export def longText (b : Bool) : Text := {literal}\n\n\
         export def firstTwo (b : Bool) : List Char := firstTwoOf {literal}\n\n\
         def firstTwoOf : Text -> List Char\n  \
         | MkText (Cons a (Cons b rest)) => [a, b]\n  \
         | t => []\n\n\
         export def longChars (b : Bool) : List Char := Text.toList {literal}\n"
    );
    let mut session = Session::new();
    if let Err(errors) = session.load("long.sw", &source) {
        panic!("{:?}", errors.iter().map(|d| d.code).collect::<Vec<_>>());
    }
    let g = &session.elab.globals;
    let native = stitchwort_js::generate(g, Limits::default()).expect("extraction succeeds");
    let list =
        stitchwort_js::generate_with(g, Limits::default(), LIST_TEXT).expect("extraction succeeds");
    assert!(native.js.contains("\"\\u{1f600}\\\"\\\\\\u{a}a"));
    assert!(
        list.js
            .contains("chars: charsOfText(\"\\u{1f600}\\\"\\\\\\u{a}a")
    );
    let script = r#"
import * as native from "./native.mjs";
import * as list from "./list.mjs";
import assert from "node:assert/strict";

const expected = "\u{1F600}\"\\\naa".repeat(50000);
for (const m of [native, list]) {
  assert.equal(m.longText(true), expected);
  assert.deepEqual(m.firstTwo(true), ["\u{1F600}", "\""]);
  const cs = m.longChars(true);
  assert.equal(cs.length, 300000);
  assert.equal(cs.join(""), expected);
}
console.log("ok");
"#;
    run_script_on(
        "long-literals",
        &[("native.mjs", native.js), ("list.mjs", list.js)],
        script,
    );
}

/// SW-335: `==` on `Text` inside a lambda argument that is checked after the
/// later arguments (its parameter's type isn't known until `xs` is) used to
/// be written out as `Text.decEqFrom … (List.decEq … (Text.toList a) …)`,
/// comparing character lists, instead of the call of `Text.decEq`, which is
/// native in generated code.
#[test]
fn an_inlined_text_comparison_calls_the_native() {
    let source = "import Std (Eq, List, Option, Text)\n\n\
        type Item = { id: Text, n: Nat }\n\n\
        export def countWith (xs: List Item) (target: Text): Nat :=\n  \
        List.length (List.filter (r => r.id == target) xs)\n\n\
        export def findWith (xs: List Item) (target: Text): Nat :=\n  \
        Option.getOrElse 0 (Option.map (r => r.n) (List.find (r => r.id == target) xs))\n";
    let mut session = Session::new();
    if let Err(errors) = session.load("compare.sw", source) {
        panic!("{:?}", errors.iter().map(|d| d.code).collect::<Vec<_>>());
    }
    let g = &session.elab.globals;
    let js = stitchwort_js::generate(g, Limits::default())
        .expect("extraction succeeds")
        .js;
    for name in ["countWith", "findWith"] {
        let line = js
            .lines()
            .find(|l| l.starts_with(&format!("const $Main$d{name} =")))
            .unwrap_or_else(|| panic!("no definition of {name}"));
        assert!(line.contains("$Std$dText$ddecEq("), "{line}");
        assert!(
            !line.contains("decEqFrom")
                && !line.contains("List$ddecEq")
                && !line.contains("toList")
                && !line.contains("charsOfText"),
            "{name} compares characters: {line}"
        );
    }
    let script = r#"
import * as m from "./compare.mjs";
import assert from "node:assert/strict";
const xs = [{ id: "a", n: 1n }, { id: "b", n: 2n }, { id: "b", n: 3n }];
assert.equal(m.countWith(xs, "b"), 2n);
assert.equal(m.countWith(xs, "c"), 0n);
assert.equal(m.findWith(xs, "a"), 1n);
assert.equal(m.findWith(xs, "z"), 0n);
console.log("ok");
"#;
    run_script_on("compare", &[("compare.mjs", js)], script);
}

/// SW-343: the same comparison as the scrutinee of a `match` (a lifted
/// helper's call, whose argument was read back from its value, unfolding
/// `Text.decEq` and everything else the lambda calls), with the key taken by
/// a function defined by pattern matching, alone and inside another function.
#[test]
fn a_text_comparison_in_a_match_scrutinee_calls_the_native() {
    let source = "import Std (Eq, List, Option, Text, Nat, Int)\n\n\
        type Thing =\n  \
        | A (ref: Nat) (id: Text) (start: Int)\n  \
        | B (ref: Nat) (id: Text) (start: Int) (label: Text)\n\n\
        def thingId: Thing -> Text\n  \
        | A _ id _ => id\n  \
        | B _ id _ _ => id\n\n\
        def findThing (id: Text) (xs: List Thing): Option Thing :=\n  \
        xs.find (t => thingId t == id)\n\n\
        export def viaHelper (id: Text) (xs: List Thing): Nat :=\n  \
        match findThing id xs with\n    \
        | None => 0\n    \
        | Some (A r _ _) => r\n    \
        | Some (B r _ _ _) => r + 100\n\n\
        export def direct (id: Text) (xs: List Thing): Nat :=\n  \
        match List.find (t => thingId t == id) xs with\n    \
        | None => 0\n    \
        | Some _ => 1\n";
    let mut session = Session::new();
    if let Err(errors) = session.load("scrutinee.sw", source) {
        panic!("{:?}", errors.iter().map(|d| d.code).collect::<Vec<_>>());
    }
    let g = &session.elab.globals;
    let js = stitchwort_js::generate(g, Limits::default())
        .expect("extraction succeeds")
        .js;
    for name in ["viaHelper", "direct"] {
        let line = js
            .lines()
            .find(|l| l.starts_with(&format!("const $Main$d{name} =")))
            .unwrap_or_else(|| panic!("no definition of {name}"));
        assert!(
            !line.contains("decEqFrom")
                && !line.contains("List$ddecEq")
                && !line.contains("toList")
                && !line.contains("charsOfText"),
            "{name} compares characters: {line}"
        );
    }
    let script = r#"
import * as m from "./scrutinee.mjs";
import assert from "node:assert/strict";
assert.equal(m.viaHelper("a", []), 0n);
assert.equal(m.direct("a", []), 0n);
console.log("ok");
"#;
    run_script_on("scrutinee", &[("scrutinee.mjs", js)], script);
}

/// Every native integer operation, and the same operations compiled from
/// their definitions (`DATA_INT`), must agree with each other and with
/// `BigInt` arithmetic written out here, on all small pairs, values around
/// the 64- and 128-bit boundaries, and seeded pseudo-random big values. Each
/// division convention must satisfy `a == d*q + r` and its range law.
#[test]
fn int_natives_agree_with_the_definitions() {
    let examples = examples();
    let g = &example(&examples, "integers.sw").elab.globals;
    let module = |options| {
        stitchwort_js::generate_with(g, Limits::default(), options)
            .expect("extraction succeeds")
            .js
    };
    let script = r#"
import * as native from "./native.mjs";
import * as data from "./data.mjs";
import assert from "node:assert/strict";

let checked = 0;
const same = (actual, expected, what) => {
  checked += 1;
  assert.deepEqual(actual, expected, what);
};
const abs = (x) => (x < 0n ? -x : x);
const sgn = (x) => (x > 0n ? 1n : x < 0n ? -1n : 0n);

// Seeded generator (xorshift), so failures reproduce.
let state = 0x2545f4914f6cdd1dn;
const next = () => {
  state ^= (state << 13n) & 0xffffffffffffffffn;
  state ^= state >> 7n;
  state ^= (state << 17n) & 0xffffffffffffffffn;
  return state;
};
const randomBig = () => {
  const bits = Number(next() % 200n) + 1;
  let v = 0n;
  for (let i = 0; i < bits; i += 32) v = (v << 32n) | (next() & 0xffffffffn);
  v &= (1n << BigInt(bits)) - 1n;
  return next() % 2n === 0n ? v : -v;
};

const small = [];
for (let i = -12n; i <= 12n; i++) small.push(i);
const big = [];
for (const k of [64n, 128n]) {
  for (const d of [-1n, 0n, 1n]) {
    big.push((1n << k) + d, -((1n << k) + d));
  }
}
for (let i = 0; i < 20; i++) big.push(randomBig());
const all = [...small, ...big];
// Small by small, then big by small and big, and small by big.
const pairs = [
  ...small.flatMap((a) => small.map((b) => [a, b])),
  ...big.flatMap((a) => all.map((b) => [a, b])),
  ...small.flatMap((a) => big.map((b) => [a, b])),
];

// Independent definitions, from the laws rather than from `/` and `%`.
const euclid = (a, d) => {
  const r = ((a % abs(d)) + abs(d)) % abs(d);
  return [(a - r) / d, r];
};
const floored = (a, d) => {
  const r = ((a % d) + d) % d;
  return [(a - r) / d, r];
};
const truncated = (a, d) => [a / d, a % d];

const refusesZero = (m, name, ...args) =>
  assert.throws(() => m[name](...args), (e) => e instanceof m.StitchwortInputError);

for (const m of [native, data]) {
  for (const name of ["eucDiv", "eucMod", "tdiv", "tmod", "fdiv", "fmod", "modNat"]) {
    for (const a of all) {
      refusesZero(m, name, a, 0n);
      checked += 1;
    }
  }
}

for (const [a, b] of pairs) {
  const tag = (op) => `${op} ${a} ${b}`;
  for (const f of ["add", "sub", "mul", "decEq", "leq", "less", "compare"]) {
    same(data[f](a, b), native[f](a, b), tag(f) + " (data)");
  }
  same(native.add(a, b), a + b, tag("add"));
  same(native.sub(a, b), a - b, tag("sub"));
  same(native.mul(a, b), a * b, tag("mul"));
  same(native.decEq(a, b), a === b, tag("decEq"));
  same(native.leq(a, b), a <= b, tag("leq"));
  same(native.less(a, b), a < b, tag("less"));
  same(native.compare(a, b), { tag: a < b ? "Less" : a === b ? "Equal" : "Greater" }, tag("compare"));
  if (b === 0n) continue;
  const d = b;
  for (const [div, mod, convention, range] of [
    ["eucDiv", "eucMod", euclid, (r) => r >= 0n && r < abs(d)],
    ["tdiv", "tmod", truncated, (r) => abs(r) < abs(d) && (r === 0n || sgn(r) === sgn(a))],
    ["fdiv", "fmod", floored, (r) => abs(r) < abs(d) && (r === 0n || sgn(r) === sgn(d))],
  ]) {
    const [q, r] = convention(a, d);
    same(native[div](a, d), q, tag(div));
    same(native[mod](a, d), r, tag(mod));
    same(data[div](a, d), q, tag(div) + " (data)");
    same(data[mod](a, d), r, tag(mod) + " (data)");
    same(a, d * q + r, `${a} = ${d}*${q} + ${r}`);
    same(range(r), true, `${mod} ${a} ${d} = ${r} is in range`);
  }
  if (d > 0n) {
    const [, r] = euclid(a, d);
    same(native.modNat(a, d), r, tag("modNat"));
    same(data.modNat(a, d), r, tag("modNat") + " (data)");
  }
}

for (const a of all) {
  const tag = (op) => `${op} ${a}`;
  for (const [f, expected] of [
    ["neg", -a],
    ["natAbs", abs(a)],
    ["abs", abs(a)],
    ["toNat", a < 0n ? 0n : a],
    ["toNatChecked", a < 0n ? undefined : a],
    ["sign", sgn(a)],
    ["toText", a.toString()],
  ]) {
    same(native[f](a), expected, tag(f));
    same(data[f](a), expected, tag(f) + " (data)");
  }
  if (a >= 0n) {
    same(native.ofNat(a), a, tag("ofNat"));
    same(data.ofNat(a), a, tag("ofNat") + " (data)");
  }
  // The round trip.
  same(native.parse(native.toText(a)), a, tag("parse . toText"));
  same(data.parse(data.toText(a)), a, tag("parse . toText") + " (data)");
}

// The grammar: an optional `-`, then one or more ASCII digits, nothing else.
const cases = ["", "-", "0", "-0", "007", "-007", "+5", " 5", "5 ", "--5", "0x10", "1e3", "12abc",
  "-12", "18446744073709551616", "-18446744073709551617", "٥", "5\n", "-+5", "1_000"];
for (const t of cases) {
  const expected = /^-?[0-9]+$/.test(t) ? BigInt(t) : undefined;
  same(native.parse(t), expected, `parse ${JSON.stringify(t)}`);
  same(data.parse(t), expected, `parse ${JSON.stringify(t)} (data)`);
}
same(native.parse("-0"), 0n, "-0 is 0");

assert.ok(checked > 20000, `only ${checked} checks ran`);
console.log("ok");
"#;
    run_script_on(
        "int-natives",
        &[
            ("native.mjs", module(Options::default())),
            ("data.mjs", module(DATA_INT)),
        ],
        script,
    );
}

/// An `Int` decodes only from a `bigint` of either sign, and a `Nat`
/// position still refuses a negative one, wherever each appears.
#[test]
fn int_crosses_the_boundary_strictly() {
    let examples = examples();
    let session = example(&examples, "integers.sw");
    let dts = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds")
        .dts;
    assert!(dts.contains("export declare function add(a: bigint, b: bigint): bigint;"));
    assert!(dts.contains("export declare function optionInt(arg0: bigint | undefined): bigint;"));
    assert!(
        dts.contains("export type Entry = { readonly count: bigint; readonly delta: bigint };")
    );
    assert!(!dts.contains("OfNat") && !dts.contains("NegSucc"), "{dts}");
    let script = r#"
import * as m from "./integers.mjs";
import assert from "node:assert/strict";

const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof m.StitchwortInputError && pattern.test(e.message));

// Either sign round-trips.
for (const x of [0n, 1n, -1n, 5n, -5n, 2n ** 200n, -(2n ** 200n) - 1n]) {
  assert.equal(m.add(x, 0n), x);
  assert.equal(m.neg(m.neg(x)), x);
  assert.deepEqual(m.optionInt(x), x * 2n);
  assert.deepEqual(m.negateAll([x]), [-x]);
}
assert.equal(m.add(-3n, 10n), 7n);
assert.deepEqual(m.negatives([0n, 4n]), [-1n, -5n]);
assert.deepEqual(m.ofNats([1n, 2n]), [1n, 2n]);

// Anything but a bigint is refused, a number and a numeric string included.
for (const bad of [5, "5", 5.0, null, undefined, {}, [], true, Object(5n)]) {
  refused(() => m.neg(bad), /^x: expected a bigint$/);
}
refused(() => m.add(1n, "1"), /^b: expected a bigint$/);

// Nat and Int share a representation but not a validator.
assert.deepEqual(m.apply({ count: 3n, delta: -1n }), { count: 3n, delta: 2n });
assert.deepEqual(m.apply({ count: 0n, delta: -(2n ** 100n) }), { count: 0n, delta: -(2n ** 100n) });
refused(() => m.apply({ count: -1n, delta: 1n }), /^e\.count: expected a non-negative bigint$/);
refused(() => m.apply({ count: 1n, delta: 1 }), /^e\.delta: expected a bigint$/);
refused(() => m.ofNat(-1n), /^n: expected a non-negative bigint$/);
refused(() => m.ofNats([1n, -1n]), /^ns\[1\]: expected a non-negative bigint$/);

// Inside Option and List (Option Int), in both directions.
assert.equal(m.optionInt(undefined), 0n);
assert.deepEqual(m.toNatChecked(-1n), undefined);
assert.deepEqual(m.parse("-5"), -5n);
refused(() => m.optionInt(4), /^arg0: expected a bigint$/);
refused(() => m.optionInt("4"), /^arg0: expected a bigint$/);
assert.deepEqual(
  m.negateAll([undefined, 3n, -3n]),
  [undefined, -3n, 3n],
);
refused(() => m.negateAll([undefined, 1.5]), /^xs\[1\]: expected a bigint$/);
refused(() => m.negateAll([null]), /^xs\[0\]: expected a value or undefined, not null$/);
assert.deepEqual(m.firstNeg([3n, -4n, -5n]), -4n);
console.log("ok");
"#;
    run_script("int-boundary", &[("integers.mjs", session)], script);
}

/// `SafeNat` and `SafeInt` cross as `number`s (SW-337): whole numbers within
/// 2^53 - 1, in both directions, in the declarations too. Decoding refuses a
/// `bigint`, a string, a fraction, `NaN`, an infinity and anything out of
/// range (even a whole number: beyond 2^53 - 1 it may be rounded already),
/// and accepts `-0` as 0. Encoding is exact.
#[test]
fn safe_numbers_cross_the_boundary_as_numbers() {
    let examples = examples();
    let session = example(&examples, "safe-numbers.sw");
    let dts = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds")
        .dts;
    for declaration in [
        "export declare function addSafe(a: number, b: number): number | undefined;",
        "export declare function negateSafe(a: number): number | undefined;",
        "export declare function toSafe(n: bigint): number | undefined;",
        "export type Counter = { readonly count: number; readonly delta: number };",
        "export declare function sumAll(xs: readonly number[]): number | undefined;",
    ] {
        assert!(dts.contains(declaration), "{declaration}\n{dts}");
    }
    let script = r#"
import * as m from "./safe-numbers.mjs";
import assert from "node:assert/strict";

const MAX = 9007199254740991;
const refused = (f, pattern) =>
  assert.throws(f, (e) => e instanceof m.StitchwortInputError && pattern.test(e.message));
const some = (value) => value;

// Numbers in, numbers out, exactly.
assert.deepEqual(m.addSafe(2, 3), some(5));
assert.deepEqual(m.addSafe(MAX, 0), some(MAX));
assert.deepEqual(m.addSafe(0, MAX), some(MAX));
assert.deepEqual(m.addSafe(MAX - 1, 1), some(MAX));
assert.deepEqual(m.addSafe(MAX, 1), undefined);
assert.deepEqual(m.addSafe(MAX, MAX), undefined);
assert.deepEqual(m.negateSafe(-5), some(5));
assert.deepEqual(m.negateSafe(-MAX), some(MAX));
assert.deepEqual(m.negateSafe(MAX), some(-MAX));
for (const x of [0, 1, 255, 65536, 2 ** 31, 2 ** 32 + 1, 2 ** 52 + 1, MAX]) {
  assert.deepEqual(m.sumAll([x]), some(x));
  assert.equal(typeof m.sumAll([x]), "number");
  assert.deepEqual(m.negateSafe(-x), some(x));
}
assert.deepEqual(m.sumAll([]), some(0));
assert.deepEqual(m.sumAll([1, 2, 3]), some(6));
assert.deepEqual(m.lengths(["ab", "", "cde"]), [some(2), some(0), some(3)]);

// A result is never -0, whichever way it's produced.
assert.ok(Object.is(m.negateSafe(0), 0));
assert.ok(Object.is(m.addSafe(0, 0), 0));

// `bigint` in, `number` out, and the other way: the bounds decide.
assert.deepEqual(m.toSafe(5n), some(5));
assert.deepEqual(m.toSafe(2n ** 53n - 1n), some(MAX));
assert.deepEqual(m.toSafe(2n ** 53n), undefined);
assert.deepEqual(m.toSafe(2n ** 100n), undefined);
assert.deepEqual(m.toSafeInt(-(2n ** 53n) + 1n), some(-MAX));
assert.deepEqual(m.toSafeInt(-(2n ** 53n)), undefined);
assert.deepEqual(m.toSafeInt(2n ** 53n), undefined);
assert.deepEqual(m.toSafeInt(-7n), some(-7));

// A `-0` is the whole number 0.
assert.deepEqual(m.addSafe(-0, -0), some(0));
assert.deepEqual(m.negateSafe(-0), some(0));

// Anything but a `number` is refused, a `bigint` and a numeric string too.
for (const bad of [5n, "5", null, undefined, {}, [], true, Object(5), { valueOf: () => 5 }]) {
  refused(() => m.addSafe(bad, 1), /^a: expected a number$/);
  refused(() => m.negateSafe(bad), /^a: expected a number$/);
}
refused(() => m.addSafe(1, 2n), /^b: expected a number$/);

// A number that isn't a whole number is refused.
for (const bad of [1.5, -1.5, 0.1, 2 ** 51 + 0.5, NaN, Infinity, -Infinity, Number.MIN_VALUE]) {
  refused(() => m.addSafe(bad, 1), /^a: expected a whole number$/);
  refused(() => m.negateSafe(bad), /^a: expected a whole number$/);
}

// Out of range, at the very edge and far beyond. 2^53 is a whole number a
// `number` holds, and so is 2^53 + 2, but not 2^53 + 1.
const natRange = /^a: expected a whole number from 0 to 9007199254740991$/;
const intRange = /^a: expected a whole number from -9007199254740991 to 9007199254740991$/;
for (const bad of [MAX + 1, MAX + 2, 2 ** 64, 1e21, Number.MAX_VALUE, -1, -MAX, -Number.MAX_VALUE]) {
  refused(() => m.addSafe(bad, 1), natRange);
}
for (const bad of [MAX + 1, MAX + 2, -MAX - 1, -MAX - 2, 2 ** 64, -(2 ** 64), 1e21, -1e21, Number.MAX_VALUE]) {
  refused(() => m.negateSafe(bad), intRange);
}

// Inside lists and records, with the path to the problem.
refused(() => m.sumAll([1, 2.5]), /^xs\[1\]: expected a whole number$/);
refused(() => m.sumAll([1, 2n]), /^xs\[1\]: expected a number$/);
refused(() => m.sumAll([1, -1]), /^xs\[1\]: expected a whole number from 0 to 9007199254740991$/);
assert.deepEqual(m.bump({ count: 41, delta: 1 }), some(42));
assert.deepEqual(m.bump({ count: 41, delta: -1 }), some(41));
refused(() => m.bump({ count: 1, delta: 1.5 }), /^c\.delta: expected a whole number$/);
refused(() => m.bump({ count: 1n, delta: 1 }), /^c\.count: expected a number$/);
refused(() => m.bump({ count: -1, delta: 1 }), /^c\.count: expected a whole number from 0 to 9007199254740991$/);
refused(() => m.bump({ count: 1, delta: 2 ** 53 }), /^c\.delta: expected a whole number from -/);
refused(() => m.bump({ count: 1 }), /^c\.delta: missing$/);

// `Nat` and `Int` are still `bigint`s.
refused(() => m.toSafe(5), /^n: expected a non-negative bigint$/);
refused(() => m.toSafeInt(5), /^n: expected a bigint$/);
console.log("ok");
"#;
    run_script("safe-numbers", &[("safe-numbers.mjs", session)], script);

    // A program's own `SafeNat` is an ordinary record, not the library's.
    let mut own = Session::new();
    own.load(
        "own.sw",
        "type SafeNat = { value: Nat, fits: value <= 9007199254740991 }\n\
         export def same (n: SafeNat): SafeNat := n\n",
    )
    .unwrap_or_else(|_| panic!("a program's own `SafeNat` checks"));
    let dts = stitchwort_js::generate(&own.elab.globals, own.elab.limits)
        .expect("extraction succeeds")
        .dts;
    assert!(
        dts.contains("export type SafeNat = { readonly value: bigint };"),
        "{dts}"
    );
}

/// The prelude with `from` replaced by `to`, which must occur.
fn changed_prelude(from: &str, to: &str) -> String {
    assert!(
        stitchwort_elab::PRELUDE.contains(from),
        "the prelude doesn't contain `{from}`"
    );
    stitchwort_elab::PRELUDE.replacen(from, to, 1)
}

fn load_example(session: &mut Session, name: &str) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/extract")
        .join(name);
    let text = std::fs::read_to_string(&path).expect("readable example");
    if let Err(diagnostics) = session.load(name, &text) {
        let rendered: String = diagnostics
            .iter()
            .map(|d| render(&session.sources, d, false))
            .collect();
        panic!("{name} doesn't check:\n{rendered}");
    }
}

/// A changed `Int.add` (same meaning and reduction, different definition, so the prelude laws still check) turns off that
/// native only: it is compiled as written, and everything else, including
/// the representation and the other natives, is as before.
#[test]
fn a_changed_int_operation_loses_only_its_native() {
    let prelude = changed_prelude(
        "| NegSucc m, NegSucc n => NegSucc (Succ (m + n))",
        "| NegSucc m, NegSucc n => NegSucc (Succ (0 + (m + n)))",
    );
    let mut session = Session::with_prelude(&prelude);
    load_example(&mut session, "integers.sw");
    let g = &session.elab.globals;
    let binding = stitchwort_js::bind_int(g).expect("hashes");
    assert!(
        binding.data.is_some() && binding.bound,
        "the data type is still bound"
    );
    let unbound: Vec<&str> = binding
        .natives
        .iter()
        .filter(|b| !b.bound)
        .map(|b| b.name)
        .collect();
    // `Int.sub` is defined with `Int.add`, so its content hash changes too: a
    // native is bound to the definition and everything it depends on.
    assert_eq!(
        unbound,
        ["Int.add", "Int.sub"],
        "only Int.add and its dependent Int.sub lose their natives"
    );

    let js = stitchwort_js::generate(g, session.elab.limits)
        .expect("extraction succeeds")
        .js;
    assert!(
        !js.contains("const $Std$dInt$dadd = (a) => (b) => a + b;"),
        "Int.add is still native"
    );
    assert!(js.contains("const $Std$dInt$dadd = "), "Int.add is defined");
    assert!(!js.contains("const $Std$dInt$dsub = (a) => (b) => a - b;"));
    assert!(js.contains("const $Std$dInt$dmul = (a) => (b) => a * b;"));
    assert!(js.contains("const INT = leaf("), "the representation is on");

    let script = r#"
import * as m from "./integers.mjs";
import assert from "node:assert/strict";
for (const [a, b] of [[0n, 0n], [3n, 4n], [-3n, 4n], [3n, -4n], [-3n, -4n], [2n ** 70n, -(2n ** 70n) - 1n], [-(2n ** 64n), -1n]]) {
  assert.equal(m.add(a, b), a + b, `add ${a} ${b}`);
  assert.equal(m.sub(a, b), a - b, `sub ${a} ${b}`);
  assert.equal(m.mul(a, b), a * b);
}
assert.equal(m.dial(-18n), 82n);
console.log("ok");
"#;
    run_script("int-changed-add", &[("integers.mjs", &session)], script);
}

/// A changed `Int` data type (here, one field renamed) turns the whole
/// representation off: `Int` is an ordinary tagged data type, with the
/// ordinary codec and `.d.ts` type and no integer natives, all consistent.
#[test]
fn a_changed_int_type_turns_the_representation_off() {
    let prelude = changed_prelude("| OfNat (n: Nat)", "| OfNat (k: Nat)");
    let mut session = Session::with_prelude(&prelude);
    load_example(&mut session, "integers.sw");
    let g = &session.elab.globals;
    let binding = stitchwort_js::bind_int(g).expect("hashes");
    assert!(!binding.bound, "the data type's hash should differ");
    let output = stitchwort_js::generate(g, session.elab.limits).expect("extraction succeeds");
    assert!(output.dts.contains("export type Int ="), "{}", output.dts);
    assert!(
        output
            .dts
            .contains("export declare function neg(x: Int): Int;"),
        "{}",
        output.dts
    );
    assert!(
        output
            .dts
            .contains(r#"{ readonly tag: "OfNat"; readonly k: bigint }"#)
    );
    for native in ["(a) => (b) => a * b", "(a) => -a", "a.toString()"] {
        assert!(
            !output.js.contains(native),
            "native `{native}` in the generated code"
        );
    }
    assert!(
        !output.js.contains("const INT = "),
        "the Int codec is still generated"
    );

    let script = r#"
import * as m from "./integers.mjs";
import assert from "node:assert/strict";

const of = (n) => (n >= 0n ? { tag: "OfNat", k: n } : { tag: "NegSucc", n: -n - 1n });
const refused = (f) => assert.throws(f, (e) => e instanceof m.StitchwortInputError);

assert.deepEqual(m.add(of(5n), of(-8n)), of(-3n));
assert.deepEqual(m.add(of(-5n), of(-8n)), of(-13n));
assert.deepEqual(m.neg(of(0n)), of(0n));
assert.deepEqual(m.mul(of(-4n), of(5n)), of(-20n));
assert.deepEqual(m.eucMod(of(-7n), of(2n)), of(1n));
assert.deepEqual(m.eucDiv(of(-7n), of(2n)), of(-4n));
assert.deepEqual(m.dial(of(-18n)), of(82n));
assert.equal(m.classify(of(0n)), "zero");
assert.equal(m.classify(of(-1n)), "minus one");
assert.equal(m.classify(of(2n)), "two");
assert.equal(m.classify(of(77n)), "positive or zero, k = 77");
assert.equal(m.classify(of(-77n)), "negative, k = 76");
assert.equal(m.toText(of(-12n)), "-12");
assert.deepEqual(m.parse("-12"), of(-12n));
assert.deepEqual(m.negatives([0n, 4n]), [of(-1n), of(-5n)]);
assert.deepEqual(m.apply({ count: 3n, delta: of(-10n) }), { count: 3n, delta: of(-7n) });
// The divisor's precondition is still checked.
refused(() => m.eucMod(of(5n), of(0n)));
// A bare bigint is no longer an Int.
refused(() => m.neg(5n));
refused(() => m.add(of(1n), 2n));
refused(() => m.neg({ tag: "OfNat", n: 5n }));
console.log("ok");
"#;
    run_script("int-changed-type", &[("integers.mjs", &session)], script);
}

/// A changed `Nat` data type (here, one field renamed) turns the number
/// representation off: `Nat` is an ordinary tagged data type, at the
/// boundary and inside generated code, and its operations are compiled from
/// their definitions rather than the natives that assume bigints.
#[test]
fn a_changed_nat_type_turns_the_representation_off() {
    let prelude = changed_prelude("| Succ (n: Nat)", "| Succ (k: Nat)");
    let mut session = Session::with_prelude(&prelude);
    session
        .load(
            "changed-nat.sw",
            "export def twice (n : Nat) : Nat := n + n\n\n\
             export def plusThree (n : Nat) : Nat := n + 3\n",
        )
        .expect("checks");
    let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds");
    assert!(output.dts.contains("export type Nat ="), "{}", output.dts);
    assert!(
        output
            .dts
            .contains(r#"readonly tag: "Succ"; readonly k: Nat"#),
        "{}",
        output.dts
    );
    assert!(
        output
            .dts
            .contains("export declare function twice(n: Nat): Nat;"),
        "{}",
        output.dts
    );
    let script = r#"
import * as m from "./changed-nat.mjs";
import assert from "node:assert/strict";

const zero = { tag: "Zero" };
const succ = (n) => ({ tag: "Succ", k: n });

assert.deepEqual(m.twice(zero), zero);
assert.deepEqual(m.twice(succ(zero)), succ(succ(zero)));
assert.deepEqual(m.plusThree(zero), succ(succ(succ(zero))));
console.log("ok");
"#;
    run_script("changed-nat", &[("changed-nat.mjs", &session)], script);
}

/// A changed `Text` data type (here, its field renamed) turns the string
/// representation off: `Text` is an ordinary tagged data type, at the
/// boundary and inside generated code, and its operations are compiled from
/// their definitions rather than the text natives.
#[test]
fn a_changed_text_type_turns_the_representation_off() {
    let prelude = changed_prelude("| MkText (chars: List Char)", "| MkText (cs: List Char)");
    let mut session = Session::with_prelude(&prelude);
    session
        .load(
            "changed-text.sw",
            "export def echo (t : Text) : Text := t\n\n\
             export def greet (t : Text) : Text := \"hi\" ++ t\n",
        )
        .expect("checks");
    let output = stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds");
    assert!(output.dts.contains("export type Text ="), "{}", output.dts);
    assert!(
        output.dts.contains(r#"readonly tag: "MkText""#),
        "{}",
        output.dts
    );
    assert!(
        output
            .dts
            .contains("export declare function echo(t: Text): Text;"),
        "{}",
        output.dts
    );
    let script = r#"
import * as m from "./changed-text.mjs";
import assert from "node:assert/strict";

const text = (s) => ({ tag: "MkText", cs: [...s] });

assert.deepEqual(m.echo(text("a😀")), text("a😀"));
assert.deepEqual(m.greet(text("!")), text("hi!"));
console.log("ok");
"#;
    run_script("changed-text", &[("changed-text.mjs", &session)], script);
}
