//! The native effect runtime (docs/proposals/effect-runtime.md §9, D1162,
//! stage 4b), as `crates/cli/tests/effect_runtime.rs` tests the JS one
//! (stage 4a): the handler shapes of `examples/extract/effect-runtime.sw`
//! over 1,000,000 elements on the machine, counts of the runtime's work,
//! which must grow linearly with the input, and every `-- run:` line of
//! that file and of `effect-handlers.sw` against the reference evaluator.

use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;

use stitchwort_core::{DefId, ResourceError, Term};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::effect::EffectCounts;
use stitchwort_rt::value::Value;
use stitchwort_rt::{Limits, Machine, Program, lower_global, lower_main};
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
        Check::OkTwice => {
            let xs = numbers(p, ok(v));
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
];

fn args(name: &str, p: &Program, n: u64) -> Vec<Value> {
    let xs = list(p, n);
    if name == "forwarded" {
        vec![Value::Nat(10), xs]
    } else {
        vec![xs]
    }
}

/// Every shape runs natively at 1,000,000 elements with the right answer,
/// within the default limits; so do the empty-row writer and search, which
/// stage 4a leaves at JS's stack limit (the machine's frames are on the
/// heap), and the empty-row state handler. `failsLast` performs its one
/// operation at the very end, with the whole list pending.
#[test]
fn every_shape_runs_at_a_million_elements() {
    with_stack(STACK, || {
        let (session, _) = example("effect-runtime.sw");
        let n = 1_000_000;
        let limits = Limits::from_core(session.elab.limits);
        let empty_row: &[(&str, Check)] =
            &[("emitted", Check::Plus(0)), ("counted", Check::Plus(0))];
        for (name, how) in SHAPES.iter().chain(empty_row) {
            let export = Export::new(&session, name);
            let p = &export.program;
            let start = Instant::now();
            let (result, _) = export.call(limits, args(name, p, n));
            let elapsed = start.elapsed();
            let v = result.unwrap_or_else(|e| panic!("{name}: {e}"));
            match name {
                // Each element is numbered twice its index (`x + next()`).
                &"counted" => {
                    let xs = numbers(p, &v);
                    assert_eq!(xs.len() as u64, n);
                    assert!(xs.iter().enumerate().all(|(i, x)| *x == 2 * i as u64));
                }
                _ => check(p, name, *how, n, &v),
            }
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
                ]);
                last = c;
            }
            for (i, key) in ["steps", "pushes", "pops", "routes", "resumes", "binds"]
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
        for name in ["effect-runtime.sw", "effect-handlers.sw"] {
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
