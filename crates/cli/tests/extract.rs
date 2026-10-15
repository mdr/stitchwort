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

use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use stitchwort_cli::driver::Session;
use stitchwort_cli::render::render;
use stitchwort_core::value::{apply, eval, force};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Limits, Term, Value};
use stitchwort_js::{Boundary, boundary_literal, exportable, field_boundaries, js_string_literal};
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
            let fields = ctors[c]
                .iter()
                .map(|(_, f)| random_value(g, f, rng, depth.saturating_sub(1)))
                .collect();
            Value::Ctor(*d, c, fields)
        }
        Boundary::Param(_) => panic!("a boundary type of an export has no parameters"),
    }
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
assert.throws(() => shapes.area({}), / arg0: unknown tag undefined; expected "Square" or "Rect"$/);
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

/// Runs a Node script, next to the generated modules it imports, and
/// requires it to print `ok`.
fn run_script(name: &str, modules: &[(&str, &Session)], script: &str) {
    let dir = std::env::temp_dir().join(format!("stitchwort-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    for (file, session) in modules {
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

// Nested inside a list, the prelude's `Maybe` and `Pair`, and a user's type,
// with the path to the problem.
refused(() => m.fromChars(["a", "\uD800"]), /^cs\[1\]: a lone surrogate/);
refused(() => m.joinOn(",", ["ok", "x\uDFFF"]), /^ts\[1\]: a lone surrogate \(U\+DFFF\) at index 1/);
refused(() => m.orEmpty({ tag: "Just", value: "\uD800" }), /^arg0\.value: a lone surrogate/);
refused(() => m.firstOf({ tag: "MkPair", fst: "a", snd: "\uDBFF" }), /^p\.snd: a lone surrogate/);
refused(() => m.greet({ tag: "MkPerson", name: "\uDC00", initial: "x", tags: [] }), /^arg0\.name: a lone surrogate/);
refused(() => m.greet({ tag: "MkPerson", name: "x", initial: "xy", tags: [] }), /^arg0\.initial: expected exactly one character, but the string has 2$/);
refused(() => m.greet({ tag: "MkPerson", name: "x", initial: "x", tags: ["\uD800"] }), /^arg0\.tags\[0\]: a lone surrogate/);
assert.equal(m.greet({ tag: "MkPerson", name: "Zoë", initial: "\u{1F600}", tags: [] }), "Hello, Zoë (\u{1F600})");
assert.deepEqual(m.uncons("\u{1F600}x"), { tag: "Just", value: { tag: "MkPair", fst: "\u{1F600}", snd: "x" } });

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

/// Long inputs in generated JS. Tail calls to the same function are loops,
/// so they handle any length. Other recursion uses a JS stack frame per
/// character (or element, or level of nesting); running out of stack is a
/// `StitchwortResourceError`, after which the module still works. The
/// text-and-IO proposal records the measured limits: a few thousand
/// characters, so 1,000 must work everywhere.
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
assert.equal(text.trim(" ".repeat(100000) + "x" + " ".repeat(100000)), "x");
assert.equal(text.fromNat(10n ** 20000n).length, 20001);

const exhausted = (f, name) =>
  assert.throws(f, (e) =>
    e instanceof text.StitchwortResourceError || e instanceof trees.StitchwortResourceError
      ? new RegExp(`^${name}: ran out of resources`).test(e.message) && e.cause instanceof RangeError
      : false);
const long = "a".repeat(1000000);
exhausted(() => text.len(long), "len");
exhausted(() => text.split(",", long), "split");
exhausted(() => text.countChar("a", long), "countChar");
let deep = { tag: "Leaf" };
for (let i = 0; i < 1000000; i++) deep = { tag: "Node", left: deep, right: { tag: "Leaf" } };
exhausted(() => trees.leaves(deep), "leaves");
// Input errors are still input errors.
assert.throws(() => text.len("\uD800"), text.StitchwortInputError);

// Afterwards, everything still works.
assert.equal(text.len("abc"), 3n);
assert.equal(trees.leaves({ tag: "Node", left: { tag: "Leaf" }, right: { tag: "Leaf" } }), 2n);

const k = "a,\u{1F600} ".repeat(250);
assert.equal(text.len(k), 1000n);
assert.equal(text.split(",", k).length, 251);
assert.equal(text.joinOn(",", text.split(",", k)), k);
assert.equal(text.join(k, k).length, 2 * k.length);
assert.equal(text.trim(k), k.slice(0, -1));
assert.equal(text.same(k, k), true);
assert.deepEqual(text.order(k, k), { tag: "Equal" });
assert.equal(text.countChar("a", k), 250n);
assert.equal(text.fromChars(text.chars(k)), k);
assert.deepEqual(text.toNat("7".repeat(1000)), { tag: "Just", value: BigInt("7".repeat(1000)) });
assert.equal(text.fromNat(10n ** 999n).length, 1000);
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

// A zigzag path doesn't repeat, so its middle is left out.
let zigzag = { tag: "Node", left: { tag: "Leaf" }, right: 7 };
for (let i = 0; i < N; i++) {
  zigzag = i % 2 === 0
    ? { tag: "Node", left: zigzag, right: { tag: "Leaf" } }
    : { tag: "Node", left: { tag: "Leaf" }, right: zigzag };
}
refused(() => m.echoTree(zigzag),
  /^t\.right\.left\.right\.left\.right\.left…\(999989 more steps\)…\.left\.right\.left\.right\.left\.right: expected a Tree object$/);

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

/// A type without constructors has no values: its declaration is `never`,
/// and the decoder says so.
#[test]
fn a_type_without_values_refuses_everything() {
    let source = "type Never : Type\n\nexport\nfromNever : Never -> Nat\nfromNever n = 0\n";
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
            let mut field_types = vec!["Nat", "Text", "Bool", "Char", "List Nat", "Maybe Text"];
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
            let _ = writeln!(source, "\nexport\n{export} : ({param} : {ty}) -> {ty}");
            for (ctor, fields) in &ctors {
                let vars: Vec<String> = (0..fields.len()).map(|i| format!("y{i}")).collect();
                let vars = vars.join(" ");
                let _ = writeln!(source, "{export} ({ctor} {vars}) = {ctor} {vars}");
            }
            source.push('\n');
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
                    "{{ const input = {literal}; check(input); const r = m.{}({literal}); check(r); assert.deepEqual(r, input); }}",
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
