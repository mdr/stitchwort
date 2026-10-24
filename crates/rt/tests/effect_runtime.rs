//! The native effect runtime (docs/proposals/effect-runtime.md §9, D1162,
//! stages 4b and 4d), as `crates/cli/tests/effect_runtime.rs` tests the JS
//! one: the handler shapes of `examples/extract/effect-runtime.sw` over
//! 1,000,000 elements on the machine, counts of the runtime's work, which
//! must grow linearly with the input, which state-passing handlers run as a
//! loop, and every `-- run:` line of that file, `effect-handlers.sw` and
//! `effect-state.sw` against the reference evaluator.

use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;

use stitchwort_core::{DefId, ResourceError, Term};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::effect::EffectCounts;
use stitchwort_rt::value::Value;
use stitchwort_rt::{
    Limits, Machine, Outcome, Policy, Program, RouteCounts, lower_global, lower_main,
    run_main_counting,
};
use stitchwort_syntax::parse_expression;

const STACK: usize = 256 * 1024 * 1024;

fn example(name: &str) -> (Session, String) {
    let path: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/extract")
        .join(name);
    let text = std::fs::read_to_string(&path).expect("readable example");
    let mut session = Session::for_stack(STACK);
    session
        .load(name, &text)
        .unwrap_or_else(|e| panic!("{name} doesn't check: {e:?}"));
    (session, text)
}

fn def_named(session: &Session, name: &str) -> DefId {
    let g = &session.elab.globals;
    (0..g.defs.len())
        .map(DefId)
        .rfind(|id| &*g.def(*id).name == name)
        .unwrap_or_else(|| panic!("no definition `{name}`"))
}

/// An export of `effect-runtime.sw`, lowered, and the machine that runs it.
struct Export {
    program: Program,
}

impl Export {
    fn new(session: &Session, name: &str) -> Export {
        let g = &session.elab.globals;
        let program = lower_global(g, session.elab.limits, def_named(session, name))
            .unwrap_or_else(|e| panic!("lowering {name}: {e:?}"));
        Export { program }
    }

    /// The export applied to `args` on a fresh machine with `limits`: the
    /// result, and the runtime's counts.
    fn call(
        &self,
        limits: Limits,
        args: Vec<Value>,
    ) -> (Result<Value, ResourceError>, EffectCounts) {
        let mut m = Machine::new(&self.program, limits);
        let f = m.entry().expect("the export's value");
        m.reset_effect_counts();
        let result = m.call(f, args);
        (result, m.effect_counts())
    }
}

/// The list `[0, 1, …, n - 1]` as the machine's value.
fn list(p: &Program, n: u64) -> Value {
    let s = &p.shapes;
    let mut xs = Value::Tag(s.nil);
    for i in (0..n).rev() {
        xs = Value::data(s.cons, [Value::Nat(i), xs]);
    }
    xs
}

/// The elements of a list of numbers.
fn numbers(p: &Program, mut xs: &Value) -> Vec<u64> {
    let s = &p.shapes;
    let mut out = Vec::new();
    loop {
        match xs {
            Value::Data(t, f) if *t == s.cons => {
                let Value::Nat(x) = f[0] else {
                    panic!("a list of numbers holds {:?}", f[0])
                };
                out.push(x);
                xs = &f[1];
            }
            Value::Tag(t) if *t == s.nil => return out,
            other => panic!("not a list: {other:?}"),
        }
    }
}

/// The elements of a list.
fn items(p: &Program, mut xs: &Value) -> Vec<Value> {
    let s = &p.shapes;
    let mut out = Vec::new();
    loop {
        match xs {
            Value::Data(t, f) if *t == s.cons => {
                out.push(f[0].clone());
                xs = &f[1];
            }
            Value::Tag(t) if *t == s.nil => return out,
            other => panic!("not a list: {other:?}"),
        }
    }
}

/// The value inside `Ok`. `Result`'s `Ok` is its first constructor.
fn ok(v: &Value) -> &Value {
    match v {
        Value::Data(0, f) => &f[0],
        other => panic!("expected `Ok`, got {other:?}"),
    }
}

/// How a shape's result is checked, for a list of `n`.
#[derive(Clone, Copy)]
enum Check {
    /// `[k, 1 + k, …]`.
    Plus(u64),
    /// `Ok [k, 1 + k, …]`.
    OkPlus(u64),
    /// `Ok [[0, 1, …]]`.
    OkOne,
    /// `Ok [0, 2, 4, …]`.
    OkTwice,
    /// `[0, 2, 4, …]`.
    Twice,
}

fn check(p: &Program, name: &str, how: Check, n: u64, v: &Value) {
    let plus = |xs: &Value, k: u64| {
        let xs = numbers(p, xs);
        assert_eq!(xs.len() as u64, n, "{name}");
        for (i, x) in xs.iter().enumerate() {
            assert_eq!(*x, i as u64 + k, "{name} at {i}");
        }
    };
    match how {
        Check::Plus(k) => plus(v, k),
        Check::OkPlus(k) => plus(ok(v), k),
        Check::OkOne => {
            let results = items(p, ok(v));
            assert_eq!(results.len(), 1, "{name}");
            plus(&results[0], 0);
        }
        Check::OkTwice | Check::Twice => {
            let v = if matches!(how, Check::OkTwice) {
                ok(v)
            } else {
                v
            };
            let xs = numbers(p, v);
            assert_eq!(xs.len() as u64, n, "{name}");
            for (i, x) in xs.iter().enumerate() {
                assert_eq!(*x, 2 * i as u64, "{name} at {i}");
            }
        }
    }
}

/// The shapes that stage 4a makes stack-safe in JS, and the result each
/// gives for `[0, …, n - 1]`. `forwarded` takes the depth first.
const SHAPES: &[(&str, Check)] = &[
    ("checked", Check::OkPlus(1)),
    ("asked", Check::Plus(7)),
    ("askedChecked", Check::OkPlus(7)),
    ("askedIn", Check::OkPlus(7)),
    ("emittedIn", Check::OkPlus(0)),
    ("searchedIn", Check::OkOne),
    ("countedIn", Check::OkTwice),
    ("forwarded", Check::Plus(7)),
    // State-passing handlers at the empty row, run as a loop (stage 4d).
    ("counted", Check::Twice),
    ("countedChecked", Check::OkTwice),
    ("countedOpen", Check::Twice),
    ("logged", Check::Plus(0)),
];

/// The state-passing handlers among [`SHAPES`]: each operation is a jump of
/// the handler's loop (stage 4d).
const STATE_SHAPES: &[&str] = &["counted", "countedChecked", "countedOpen", "logged"];

fn args(name: &str, p: &Program, n: u64) -> Vec<Value> {
    let xs = list(p, n);
    if name == "forwarded" {
        vec![Value::Nat(10), xs]
    } else if name == "countedChecked" {
        vec![Value::Nat(n), xs]
    } else {
        vec![xs]
    }
}

/// Every shape runs natively at 1,000,000 elements with the right answer,
/// within the default limits; so do the empty-row writer and search, which
/// stage 4a leaves at JS's stack limit (the machine's frames are on the
/// heap). `failsLast` performs its one operation at the very end, with the
/// whole list pending.
#[test]
fn every_shape_runs_at_a_million_elements() {
    with_stack(STACK, || {
        let (session, _) = example("effect-runtime.sw");
        let n = 1_000_000;
        let limits = Limits::from_core(session.elab.limits);
        let empty_row: &[(&str, Check)] = &[("emitted", Check::Plus(0))];
        for (name, how) in SHAPES.iter().chain(empty_row) {
            let export = Export::new(&session, name);
            let p = &export.program;
            let start = Instant::now();
            let (result, _) = export.call(limits, args(name, p, n));
            let elapsed = start.elapsed();
            let v = result.unwrap_or_else(|e| panic!("{name}: {e}"));
            check(p, name, *how, n, &v);
            eprintln!("{name}\t{} ms", elapsed.as_millis());
        }
        let export = Export::new(&session, "searched");
        let p = &export.program;
        let (result, _) = export.call(limits, vec![list(p, n)]);
        let v = result.expect("searched");
        assert_eq!(items(p, &v).len(), 1);
        let export = Export::new(&session, "failsLast");
        let p = &export.program;
        let (result, _) = export.call(limits, vec![Value::Nat(n), list(p, n)]);
        match result.expect("failsLast") {
            Value::Data(1, f) => assert!(matches!(&f[0], Value::Text(t) if &**t == "last")),
            other => panic!("failsLast: {other:?}"),
        }
    });
}

/// The runtime's work grows linearly: run-loop steps, pushes and pops of
/// pending continuations, routes and resumptions per element are the same
/// at 1,000, 10,000 and 100,000 elements (so nothing rebuilds a pending list
/// or rescans it), and an operation is routed through each handler and
/// `translate` it crosses once, however long the pending list is.
#[test]
fn the_work_per_element_is_constant() {
    with_stack(STACK, || {
        let (session, _) = example("effect-runtime.sw");
        let limits = Limits::from_core(session.elab.limits);
        for (name, how) in SHAPES {
            let export = Export::new(&session, name);
            let p = &export.program;
            let mut per = Vec::new();
            let mut last = EffectCounts::default();
            for n in [1_000, 10_000, 100_000] {
                let (result, c) = export.call(limits, args(name, p, n));
                check(p, name, *how, n, &result.expect(name));
                let f = |x: u64| x as f64 / n as f64;
                per.push([
                    f(c.steps),
                    f(c.pushes),
                    f(c.pops),
                    f(c.routes),
                    f(c.resumes),
                    f(c.binds),
                    f(c.jumps),
                ]);
                if STATE_SHAPES.contains(name) {
                    // Every operation is a jump of the handler's loop, and none
                    // a resumption by a call (`countedChecked`'s `Fail` handler
                    // resumes each `next` it forwards lazily, a node each).
                    assert_eq!(c.jumps, n, "{name}: jumps at {n}");
                    if *name != "countedChecked" {
                        assert_eq!(c.resumes, 0, "{name}: resumptions at {n}");
                    }
                } else {
                    assert_eq!(c.jumps, 0, "{name}: jumps at {n}");
                }
                last = c;
            }
            for (i, key) in [
                "steps", "pushes", "pops", "routes", "resumes", "binds", "jumps",
            ]
            .iter()
            .enumerate()
            {
                let (small, large) = (per[0][i], per[2][i]);
                assert!(
                    large <= small + 0.01,
                    "{name}: {key} per element grew from {small} to {large}"
                );
                // `forwarded`'s operations each cross eleven handlers.
                let crossed = if *name == "forwarded" { 11.0 } else { 1.0 };
                assert!(
                    large <= 40.0 * crossed,
                    "{name}: {key} per element is {large}"
                );
            }
            assert_eq!(last.pushes, last.pops, "{name}: pushes and pops differ");
            eprintln!("{name}: {last:?}");
        }
    });
}

/// `bind (Done x) k` is `k x`, called directly: the native backend's
/// invariant (§9.1.4). `checked`'s callback never performs anything, so
/// none of its binds makes a node, and the fold's loop runs once.
#[test]
fn bind_of_done_is_a_direct_call() {
    with_stack(STACK, || {
        let (session, _) = example("effect-runtime.sw");
        let limits = Limits::from_core(session.elab.limits);
        let export = Export::new(&session, "checked");
        let p = &export.program;
        let (result, c) = export.call(limits, vec![list(p, 100_000)]);
        check(
            p,
            "checked",
            Check::OkPlus(1),
            100_000,
            &result.expect("checked"),
        );
        assert_eq!(
            c,
            EffectCounts {
                steps: 1,
                ..EffectCounts::default()
            }
        );
    });
}

/// The list of these numbers, as the machine's value.
fn nat_list(p: &Program, xs: &[u64]) -> Value {
    let s = &p.shapes;
    let mut out = Value::Tag(s.nil);
    for x in xs.iter().rev() {
        out = Value::data(s.cons, [Value::Nat(*x), out]);
    }
    out
}

/// Which handlers of `effect-state.sw` run as a loop (stage 4d,
/// `stitchwort_rt::fusion`), told by the jumps their operations make: a
/// state-passing handler at the empty row with a tail resumption, whatever
/// else its clauses do with `k`; not one with an ability outside it, nor
/// one with a clause that isn't `Done` of a function at the closed empty
/// row, nor one that never resumes in tail position. (Their answers are the
/// reference evaluator's: `run_lines_agree_with_the_reference_evaluator`.)
#[test]
fn state_handlers_run_as_a_loop_where_they_fit() {
    with_stack(STACK, || {
        let (session, _) = example("effect-state.sw");
        let limits = Limits::from_core(session.elab.limits);
        let codes: &[u64] = &[0, 2, 3, 4, 5, 1, 0];
        // The export, its list argument, and the jumps it makes.
        let cases: &[(&str, &[u64], u64)] = &[
            // `tick` jumps; `both` resumes twice by calls, and in each branch
            // `many 3` three times; each of those six runs a `branch`, a jump,
            // and a `mixed`, a jump unless the state is 0 there, which it is
            // in three: 1 + 6 + 3 = 10.
            ("tallied", codes, 10),
            ("talliedOpen", codes, 10),
            ("talliedChecked", codes, 0),
            // `get`, `put` and `get` again for each element.
            ("stores", &[4, 0, 7], 9),
            ("storesEta", &[4, 0, 7], 0),
            ("storesEtaOpen", &[4, 0, 7], 9),
            ("nestedState", &[1, 2, 3], 3),
            ("stateInState", &[1, 2, 3], 3),
        ];
        for (name, xs, jumps) in cases {
            let export = Export::new(&session, name);
            let p = &export.program;
            let (result, c) = export.call(limits, vec![nat_list(p, xs)]);
            result.unwrap_or_else(|e| panic!("{name}: {e}"));
            assert_eq!(c.jumps, *jumps, "{name}: {c:?}");
        }
        let export = Export::new(&session, "stored");
        let (result, c) = export.call(limits, vec![Value::Nat(3)]);
        result.expect("stored");
        assert_eq!(c.jumps, 0, "stored: {c:?}");
    });
}

/// Routing costs a constant per operation and handler crossed: `ask`
/// crosses `depth` handlers of another ability (each with a `translate`) on
/// its way to the reader, whatever the length of the list.
#[test]
fn routing_is_per_handler_crossed() {
    with_stack(STACK, || {
        let (session, _) = example("effect-runtime.sw");
        let limits = Limits::from_core(session.elab.limits);
        let export = Export::new(&session, "forwarded");
        let p = &export.program;
        for depth in [1u64, 10, 100] {
            let mut per = Vec::new();
            for n in [1_000, 10_000] {
                let (result, c) = export.call(limits, vec![Value::Nat(depth), list(p, n)]);
                check(
                    p,
                    "forwarded",
                    Check::Plus(7),
                    n,
                    &result.expect("forwarded"),
                );
                per.push(c.routes as f64 / (n * (depth + 1)) as f64);
            }
            assert!(
                per[1] <= per[0] + 0.01,
                "forwarded {depth}: routes grew from {} to {}",
                per[0],
                per[1]
            );
            assert!(per[1] <= 3.0, "forwarded {depth}: {} routes", per[1]);
            eprintln!(
                "forwarded {depth}: {} routes per operation and handler",
                per[1]
            );
        }
    });
}

/// The empty-row writer and search consume each resumption's result in pure
/// code (`Cons v (k ())`), so they nest a frame per operation: they run up
/// to the frame limit, and past it end with the depth resource error, the
/// machine's documented limit (§9.1.7; the JS backend's is its stack). If
/// this starts to pass, the limit has moved: update the note and this test.
#[test]
fn empty_row_non_tail_handlers_run_up_to_the_frame_limit() {
    with_stack(STACK, || {
        let (session, _) = example("effect-runtime.sw");
        let limits = Limits {
            frames: 100_000,
            ..Limits::from_core(session.elab.limits)
        };
        for name in ["emitted", "searched"] {
            let export = Export::new(&session, name);
            let p = &export.program;
            let (result, _) = export.call(limits, vec![list(p, 10_000)]);
            assert!(result.is_ok(), "{name} at 10,000");
            let (result, _) = export.call(limits, vec![list(p, 1_000_000)]);
            assert!(
                matches!(result, Err(ResourceError::Depth)),
                "{name} at 1,000,000 with 100,000 frames: {result:?}"
            );
        }
    });
}

/// Structural equality of two of the machine's values without functions.
fn same(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Data(t, f), Value::Data(u, g)) => {
            t == u && f.len() == g.len() && f.iter().zip(g.iter()).all(|(x, y)| same(x, y))
        }
        (Value::Tag(t), Value::Tag(u)) => t == u,
        (Value::Nat(x), Value::Nat(y)) => x == y,
        (Value::BigNat(x), Value::BigNat(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::BigInt(x), Value::BigInt(y)) => x == y,
        (Value::Text(x), Value::Text(y)) => x == y,
        (Value::Float(x), Value::Float(y)) => x.to_bits() == y.to_bits(),
        (Value::Erased, Value::Erased) => true,
        _ => false,
    }
}

/// Every `-- run:` line of the effect examples gives the reference
/// evaluator's answer on the machine: the call and the reference's normal
/// form are lowered together, as a pair, and the machine's two values must
/// be equal.
#[test]
fn run_lines_agree_with_the_reference_evaluator() {
    with_stack(STACK, || {
        let mut ran = 0;
        for name in ["effect-runtime.sw", "effect-handlers.sw", "effect-state.sw"] {
            let (mut session, text) = example(name);
            for line in text.lines().filter_map(|l| l.strip_prefix("-- run:")) {
                let source = line.trim();
                let file = session.sources.add("<run>", source);
                let expr = parse_expression(file, source).expect("run line parses");
                let (term, _) = session
                    .elab
                    .infer_expr(&expr)
                    .unwrap_or_else(|d| panic!("`{source}` doesn't check: {}", d.message));
                let g = &session.elab.globals;
                let value = stitchwort_core::value::eval(g, &[], &term).expect("evaluates");
                let expected = stitchwort_core::value::quote(g, 0, &value).expect("quotes");
                let (pair, _) = g
                    .registry
                    .ctor(stitchwort_core::registry::Builtin::MkPair)
                    .expect("pairs");
                let entry = Term::Ctor(pair, 0, vec![Rc::new(term), Rc::new(expected)]);
                let program = lower_main(g, session.elab.limits, &entry)
                    .unwrap_or_else(|e| panic!("lowering `{source}`: {e:?}"));
                let mut m = Machine::new(&program, Limits::from_core(session.elab.limits));
                let got = m.entry().unwrap_or_else(|e| panic!("`{source}`: {e}"));
                let Value::Data(_, f) = &got else {
                    panic!("`{source}`: {got:?}")
                };
                assert!(
                    same(&f[0], &f[1]),
                    "{name}: `{source}`: the machine gives {:?}, the reference {:?}",
                    f[0],
                    f[1]
                );
                ran += 1;
            }
        }
        assert!(ran >= 30, "{ran}");
    });
}

/// `examples/accept/partial-forwarding.sw`'s `main`, lowered: a non-tail
/// partial recursion `depth` levels deep (the first input line) whose every
/// level prints, through handlers that forward `IO`, a translation and
/// recursion requests.
fn partial_forwarding() -> Program {
    let name = "partial-forwarding.sw";
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept")
        .join(name);
    let text = std::fs::read_to_string(&path).expect("readable example");
    let mut session = Session::for_stack(STACK);
    session
        .load(name, &text)
        .unwrap_or_else(|e| panic!("{name} doesn't check: {e:?}"));
    let main = session.main().expect("a `main`");
    lower_main(&session.elab.globals, session.elab.limits, main.term())
        .unwrap_or_else(|e| panic!("lowering {name}: {e:?}"))
}

/// What `partial-forwarding.sw` prints last for `depth`: each level adds 1
/// and the number of Collatz steps from `n % 8 + 1` to 1.
fn partial_forwarding_total(depth: u64) -> u64 {
    let collatz = |mut n: u64| {
        let mut steps = 0;
        while n != 1 {
            n = if n.is_multiple_of(2) {
                n / 2
            } else {
                3 * n + 1
            };
            steps += 1;
        }
        steps
    };
    (1..=depth).map(|n| 1 + collatz(n % 8 + 1)).sum()
}

/// Runs `partial-forwarding.sw` at `depth` with the default limits and
/// checks what it printed: every level, then the total. The routing counts.
fn run_partial_forwarding(program: &Program, depth: u64) -> RouteCounts {
    let mut output = Vec::new();
    let input = format!("{depth}\n");
    let (result, counts) = run_main_counting(
        program,
        Limits::default(),
        &Policy::default(),
        &mut input.as_bytes(),
        &mut output,
    );
    assert_eq!(result.expect("it runs"), Outcome::Finished, "at {depth}");
    let output = String::from_utf8(output).expect("text");
    let mut lines = output.lines();
    for n in (1..=depth).rev() {
        assert_eq!(lines.next(), Some(n.to_string().as_str()), "at {depth}");
    }
    let total = format!("total {}", partial_forwarding_total(depth));
    assert_eq!(lines.next(), Some(total.as_str()), "at {depth}");
    assert_eq!(lines.next(), None, "at {depth}");
    counts
}

/// The `IO` runner routes an operation by its index of `Map` and `Tie`
/// frames, never looking at the ordinary frames between them (§9.1.6, stage
/// 4c): in `partial-forwarding.sw` every `print` leaves the focus with one
/// waiting frame per level below it, so the frames below the focus per
/// operation grow with the depth, while the frames routing looks at per
/// operation stay the same, a few `Tie`s and `Map`s.
#[test]
fn routing_work_is_independent_of_control_depth() {
    with_stack(STACK, || {
        let program = partial_forwarding();
        let mut per = Vec::new();
        for depth in [1_000, 10_000, 100_000] {
            let c = run_partial_forwarding(&program, depth);
            let ops = c.operations as f64;
            eprintln!(
                "depth {depth}: {c:?}; per operation, {} visited and {} below",
                c.visited as f64 / ops,
                c.below as f64 / ops
            );
            // Many ordinary frames below each operation...
            assert!(
                c.below as f64 / ops >= depth as f64 / 8.0,
                "depth {depth}: {c:?}"
            );
            per.push(c.visited as f64 / ops);
        }
        // ...but routing looks at a few, however many.
        assert!(
            per[2] <= per[0] + 0.01,
            "visited per operation grew: {per:?}"
        );
        assert!(per[2] <= 4.0, "visited per operation: {per:?}");
    });
}

/// `Partial` mixed with other forwarded abilities, a million levels deep,
/// within the default limits (`partial-forwarding.sw`; the reference
/// evaluator and `run --js` agree with this runner on it in
/// `crates/cli/tests/run_reference.rs` and `run_js.rs`).
#[test]
fn partial_with_forwarded_abilities_runs_a_million_levels_deep() {
    with_stack(STACK, || {
        let program = partial_forwarding();
        let start = Instant::now();
        let c = run_partial_forwarding(&program, 1_000_000);
        eprintln!(
            "1,000,000 levels: {} ms, {c:?}",
            start.elapsed().as_millis()
        );
    });
}

/// A program whose `IO` operations, read replies included, go through a
/// partial recursion (`Tie` frames) and a forwarding handler.
const CROSSING: &str = "import Std (Fail, IO, Nat, Option, Result, Text)

def echo: Nat -> {IO, Partial} Nat
  | 0 => 0
  | n =>
    let line := Option.getOrElse \"none\" (IO.readLine())
    let shown := Fail.toResult (() =>
      IO.print \"${n}: ${line}\"
      if line == \"stop\" then Fail.fail \"stopped\" else Text.length line)
    match shown with
      | Ok length => length + echo (n - 1)
      | Err message => Text.length message

def main(): {IO, Partial} () :=
  IO.print \"total ${echo 4}\"
";

/// An `IO` operation crossing translation (`Map`) frames on its way to the
/// runner, which stage 4c's note found no source program makes (a
/// translation around a partial computation is crossed only by its own
/// recursion requests, E-PARTIAL): `main`'s computation wrapped in two
/// `Effect.mapSig Effect.sigSwap`s at the term level, so each operation is
/// renamed twice on the way out (`L io` to `R io` and back) and its reply
/// mapped back through both (stage 4e). The output is the unwrapped run's,
/// and routing looks at both translations for every operation.
#[test]
fn io_operations_cross_translations_on_their_way_to_the_runner() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("crossing.sw", CROSSING)
            .unwrap_or_else(|e| panic!("crossing.sw doesn't check: {e:?}"));
        let main = session.main().expect("a `main`");
        let g = &session.elab.globals;
        let limits = session.elab.limits;
        // Type arguments are erased by the definitions' types, so any term
        // will do for them.
        let erased = || Term::Sort(stitchwort_core::Sort::Type(0));
        let implicit = |id: DefId, n: usize| {
            (0..n).fold(Term::Def(id), |f, _| {
                Term::app_icit(f, erased(), stitchwort_core::Icit::Implicit)
            })
        };
        let map_sig = def_named(&session, "Effect.mapSig");
        let sig_swap = def_named(&session, "Effect.sigSwap");
        let wrap = |d: Term| Term::app(Term::app(implicit(map_sig, 5), implicit(sig_swap, 4)), d);
        let plain = lower_main(g, limits, main.term()).expect("lowering main");
        let wrapped = lower_main(g, limits, &wrap(wrap(main.term().clone())))
            .expect("lowering the wrapped main");
        let run = |program: &Program, input: &str| {
            let mut output = Vec::new();
            let (result, counts) = run_main_counting(
                program,
                Limits::default(),
                &Policy::default(),
                &mut input.as_bytes(),
                &mut output,
            );
            assert_eq!(result.expect("it runs"), Outcome::Finished);
            (String::from_utf8(output).expect("text"), counts)
        };
        for input in [
            "",
            "a\nbb\n",
            "one\ntwo\nthree\nfour\nfive\n",
            "x\nstop\ny\n",
        ] {
            let (expected, before) = run(&plain, input);
            let (output, after) = run(&wrapped, input);
            assert_eq!(output, expected, "with input {input:?}");
            assert_eq!(after.operations, before.operations, "with input {input:?}");
            // Every operation that reaches the runner crosses (or, for a
            // recursion request, is stopped inside) the two translations:
            // each `IO` operation is looked at by both.
            // The prints, and a read before each level's print.
            let lines = output.lines();
            let io =
                lines.clone().count() as u64 + lines.filter(|l| l.contains(": ")).count() as u64;
            assert!(
                after.visited >= before.visited + 2 * io,
                "with input {input:?}: {before:?} unwrapped, {after:?} wrapped"
            );
        }
        let (output, _) = run(&wrapped, "a\nbb\n");
        assert_eq!(output, "4: a\n3: bb\n2: none\n1: none\ntotal 11\n");
    });
}
