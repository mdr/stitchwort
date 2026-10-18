//! Running partial programs (docs/proposals/partial.md §7.4, §7.5, §7.8).
//!
//! The runner is compared with the executable model of the runtime rules,
//! `crates/partial-model`, on the same programs: the model's are written
//! against its typed API as the elaborator would translate them
//! (`crates/partial-model/tests/programs/mod.rs`), and here they're written
//! in Stitchwort and run by `stitchwort run`'s runner. The complete traces
//! (each operation, with its reply, and each tick, in order) must be the
//! same. Then the runner's own rules: operations are returned to it, never
//! performed inside a step; ticks and resource limits are separate; tail
//! loops run in constant space.

#[path = "../../partial-model/tests/programs/mod.rs"]
mod programs;

use programs::*;
use stitchwort_core::step::{Machine, Obs};
use stitchwort_core::value::{eval, force};
use stitchwort_driver::driver::Session;
use stitchwort_driver::run::{Event, Outcome, Policy, RunError};
use stitchwort_partial_model::runner::{self, PRINT, READ_LINE, Script};
use stitchwort_partial_model::val::Val;

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

/// Runs `main` with these input lines and tick limit: the trace, and how it
/// ended.
fn run_traced(
    session: &mut Session,
    input: &[&str],
    max_ticks: Option<u64>,
) -> (Vec<Event>, Outcome) {
    let main = session.main().expect("`main` has the right type");
    let text: String = input.iter().map(|l| format!("{l}\n")).collect();
    let mut trace = Vec::new();
    let outcome = session
        .run_main_with(
            &main,
            &mut text.as_bytes(),
            &mut std::io::sink(),
            &Policy { max_ticks },
            &mut |e| trace.push(e),
        )
        .unwrap_or_else(|e| panic!("{e}"));
    (trace, outcome)
}

/// The model's trace, as the runner's events.
fn model_trace(
    d: stitchwort_partial_model::delay::Delay,
    input: &[&str],
    max_ticks: Option<u64>,
) -> (Vec<Event>, runner::Outcome) {
    let mut host = Script::with_input(input);
    let policy = runner::Policy {
        max_ticks,
        ..runner::Policy::default()
    };
    let report = runner::run(d.clone(), &mut host, &policy);
    // The model's machine agrees with its literal transcription of the
    // equations (docs/proposals/partial.md §7.4.2), on these programs too.
    let mut host = Script::with_input(input);
    let reference = runner::run_reference(
        stitchwort_partial_model::reference::Rules::Draft3,
        d,
        &mut host,
        max_ticks.unwrap_or(u64::MAX),
    );
    assert_eq!(
        report.trace, reference.trace,
        "the model's machine and equations differ"
    );
    let events = report
        .trace
        .into_iter()
        .map(|e| match e {
            runner::Event::Tick => Event::Tick,
            runner::Event::Op(Val::Tag(PRINT, t), _) => Event::Print(t.as_text().to_string()),
            runner::Event::Op(Val::Tag(READ_LINE, _), reply) => Event::Read(match reply {
                Val::R(t) => Some(t.as_text().to_string()),
                _ => None,
            }),
            other => panic!("an operation the runner doesn't have: {other:?}"),
        })
        .collect();
    (events, report.outcome)
}

fn shown(v: &Val) -> String {
    match v {
        Val::Nat(n) => n.to_string(),
        Val::Bool(b) => if *b { "True" } else { "False" }.to_string(),
        other => panic!("unexpected result {other:?}"),
    }
}

fn ticks(trace: &[Event]) -> usize {
    trace.iter().filter(|e| **e == Event::Tick).count()
}

/// Definitions shared by the programs below, in Stitchwort.
const DEFINITIONS: &str = r#"
def immediate (n : Nat) : {Partial} Nat := n

def countdown : Nat -> {Partial} Nat
  | 0 => 0
  | n => countdown (n - 1)

def collatzSteps : Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def fib (n : Nat) : {Partial} Nat := if Nat.leq n 1 then n else fib (n - 1) + fib (n - 2)

def sumTo : Nat -> {Partial} Nat
  | 0 => 0
  | n => n + sumTo (n - 1)

def isEven : Nat -> {Partial} Bool
  | 0 => True
  | n => isOdd (n - 1)

def isOdd : Nat -> {Partial} Bool
  | 0 => False
  | n => isEven (n - 1)

def hofF : Nat -> {Partial} Nat
  | 0 => 1
  | n => n - hofM (hofF (n - 1))

def hofM : Nat -> {Partial} Nat
  | 0 => 0
  | n => n - hofF (hofM (n - 1))

def useP (k : Nat -> {Partial | e} Nat) (n : Nat) : {Partial | e} Nat := k n

def viaHelper : Nat -> {Partial} Nat
  | 0 => 1
  | n => useP viaHelper (n - 1)

def twiceWith (k : Nat -> {Partial | e} Nat) (n : Nat) : {Partial | e} Nat := k n + k n

def tree : Nat -> {Partial} Nat
  | 0 => 1
  | n => twiceWith (\x => tree x) (n - 1)

type Handlers (e : Effect.Sig) : Type =
  | MkHandlers (onStep : Nat -> {Partial | e} Nat) (onDone : Nat -> {Partial | e} Nat)

def drive : [e : Effect.Sig] -> Handlers e -> Nat -> {Partial | e} Nat
  | MkHandlers onStep onDone, 0 => onDone 0
  | MkHandlers onStep onDone, n => onStep (n - 1)

def stored (n : Nat) : {Partial} Nat := drive (MkHandlers (\y => stored y) (\u => 42)) n

def countFrom (x : Nat) : Nat -> {Partial} Nat
  | 0 => x * 10
  | n => countFrom x (n - 1)

def spin (n : Nat) : {Partial} Nat := spin n
"#;

/// A program printing `expr`, a `Nat` or a `Bool`.
fn printing(expr: &str, boolean: bool) -> String {
    let shown = if boolean {
        format!("if {expr} then \"True\" else \"False\"")
    } else {
        format!("Nat.toText ({expr})")
    };
    format!("{DEFINITIONS}\ndef main () : {{IO, Partial}} () := print ({shown})\n")
}

#[test]
fn ticks_and_results_agree_with_the_model() {
    let cases: Vec<(&str, bool, stitchwort_partial_model::delay::Delay, usize)> = vec![
        ("immediate 7", false, immediate().call(7).raw, 0),
        ("countdown 1", false, countdown().call(1).raw, 1),
        ("countdown 2", false, countdown().call(2).raw, 2),
        ("countdown 1000", false, countdown().call(1000).raw, 1000),
        ("collatzSteps 1", false, collatz_steps().call(1).raw, 0),
        ("collatzSteps 27", false, collatz_steps().call(27).raw, 111),
        ("fib 10", false, fib().call(10).raw, 176),
        ("sumTo 100", false, sum_to().call(100).raw, 100),
        ("isEven 10", true, even_odd().call((true, 10)).raw, 10),
        ("isOdd 7", true, even_odd().call((false, 7)).raw, 7),
        ("hofF 10", false, hofstadter().call((true, 10)).raw, 178),
        ("hofM 10", false, hofstadter().call((false, 10)).raw, 170),
        ("hofF 15", false, hofstadter().call((true, 15)).raw, 606),
        ("viaHelper 5", false, via_helper().call(5).raw, 5),
        ("tree 3", false, tree().call(3).raw, 14),
        ("stored 4", false, stored().call(4).raw, 4),
        ("countFrom 6 6", false, fresh_in_continuation(6).raw, 6),
    ];
    println!("| program | model ticks | runner ticks | result |");
    println!("|---|---|---|---|");
    for (expr, boolean, model, expected_ticks) in cases {
        let (model_events, model_outcome) = model_trace(model, &[], None);
        let runner::Outcome::Finished(result) = model_outcome else {
            panic!("{expr}: the model didn't finish: {model_outcome:?}");
        };
        let mut session = load(&printing(expr, boolean));
        let (events, outcome) = run_traced(&mut session, &[], None);
        assert_eq!(outcome, Outcome::Finished, "{expr}");
        let mut expected = model_events;
        expected.push(Event::Print(shown(&result)));
        assert_eq!(events, expected, "{expr}: the runner and the model differ");
        assert_eq!(ticks(&events), expected_ticks, "{expr}: ticks");
        println!(
            "| `{expr}` | {expected_ticks} | {} | {} |",
            ticks(&events),
            shown(&result)
        );
    }
}

/// Programs with input and output, in Stitchwort, and the model's
/// versions of them.
const IO_DEFINITIONS: &str = r#"
-- echo count: prints each line until the end of the input.
def echoLine (count : Nat) : Maybe Text -> (Nat -> {IO, Partial | e} Nat) -> {IO, Partial | e} Nat
  | Nothing, more => count
  | Just l,  more =>
    print l
    more (count + 1)

def echo (count : Nat) : {IO, Partial} Nat := echoLine count (readLine ()) echo

-- Operations before and after a non-tail request.
def leave (n : Nat) (r : Nat) : {IO} Nat :=
  print ("leave " ++ Nat.toText n)
  r + n

def nest (n : Nat) : {IO, Partial} Nat :=
  print ("enter " ++ Nat.toText n)
  if n == 0 then 0 else leave n (nest (n - 1))

-- A recursive function calling another.
def outer (n : Nat) : {IO, Partial} Nat := if n == 0 then 0 else nest 1 + outer (n - 1)

-- An ability handled into `IO` between requests: each `ask` reads a line.
ability Ask where
  ask : () -> {Ask} Nat

def askTwice () : {Ask} Nat := ask () + ask ()

def lineLength : Maybe Text -> Nat
  | Nothing => 0
  | Just t  => List.length (Text.toList t)

def viaReadLine (prog : () -> {Ask} Nat) : {IO} Nat :=
  handle prog () with
    | return x    => x
    | ask u, k    => k (lineLength (readLine ()))

def sumAsks : Nat -> {IO, Partial} Nat
  | 0 => 0
  | n => viaReadLine askTwice + sumAsks (n - 1)

-- Forever.
def forever (n : Nat) : {IO, Partial} Nat :=
  print "tick"
  forever (n + 1)

def spin (n : Nat) : {Partial} Nat := spin n
"#;

fn io_program(call: &str) -> String {
    format!("{IO_DEFINITIONS}\ndef main () : {{IO, Partial}} () := print (Nat.toText ({call}))\n")
}

#[test]
fn traces_with_operations_agree_with_the_model() {
    let echo_input: &[&str] = &["a", "", "b c"];
    let ask_input: &[&str] = &["x", "yy", "", "zzzz", "w"];
    let cases: Vec<(&str, stitchwort_partial_model::delay::Delay, &[&str])> = vec![
        ("echo 0", echo().call(0).raw, echo_input),
        ("echo 0", echo().call(0).raw, &[]),
        ("nest 3", nest().call(3).raw, &[]),
        ("outer 3", outer(nest()).call(3).raw, &[]),
        ("sumAsks 3", sum_asks().call(3).raw, ask_input),
    ];
    for (call, model, input) in cases {
        let (model_events, model_outcome) = model_trace(model, input, None);
        let runner::Outcome::Finished(result) = model_outcome else {
            panic!("{call}: the model didn't finish: {model_outcome:?}");
        };
        let mut session = load(&io_program(call));
        let (events, outcome) = run_traced(&mut session, input, None);
        assert_eq!(outcome, Outcome::Finished, "{call}");
        let mut expected = model_events;
        expected.push(Event::Print(shown(&result)));
        assert_eq!(events, expected, "{call} with input {input:?}");
        println!(
            "{call} with {input:?}: {} ticks, {} events",
            ticks(&events),
            events.len()
        );
    }
}

#[test]
fn endless_loops_stop_at_the_tick_limit_like_the_model() {
    for (call, model) in [
        ("forever 0", forever_print().call(0).raw),
        ("spin 0", programs::spin().call(0).raw),
    ] {
        let (model_events, model_outcome) = model_trace(model, &[], Some(50));
        assert_eq!(model_outcome, runner::Outcome::OutOfTicks);
        let mut session = load(&io_program(call));
        let (events, outcome) = run_traced(&mut session, &[], Some(50));
        assert_eq!(outcome, Outcome::OutOfTicks, "{call}: inconclusive");
        assert_eq!(events, model_events, "{call}");
        assert_eq!(ticks(&events), 50);
    }
}

/// `main ()` as a `Delay` value, to step by hand.
fn main_value(session: &mut Session) -> stitchwort_core::Value {
    let expr = session
        .parse_expression("<main>", "((\\u => main ()) : () -> {IO, Partial} ()) ()")
        .unwrap();
    let (term, _) = session.elab.infer_expr(&expr).unwrap();
    let g = &session.elab.globals;
    force(g, eval(g, &[], &term).unwrap()).unwrap()
}

/// `step` describes host requests and never performs them
/// (docs/proposals/partial.md §7.4.5): a step that reaches an operation
/// returns it, and the step goes on only when it's given a reply.
#[test]
fn a_step_returns_operations_without_performing_them() {
    let mut session = load(&io_program("echo 0"));
    let main = main_value(&mut session);
    let g = &session.elab.globals;
    let machine = Machine::start(g, main);
    let Obs::Call(op, pending) = machine.step(g).unwrap() else {
        panic!("the first thing `echo` does is read a line");
    };
    // `L (IO.%readLine ())`: an operation of `{IO}`, unperformed.
    let stitchwort_core::Value::Ctor(_, 0, io) = force(g, op).unwrap() else {
        panic!("an operation of `{{IO}}`");
    };
    let stitchwort_core::Value::Ctor(d, c, _) = force(g, io[0].clone()).unwrap() else {
        panic!("an `IO` operation");
    };
    assert_eq!(&*g.data(d).ctors[c].name, "%readLine");
    // Reply `Nothing`: `echo` finishes with 0, then `main` prints it, which
    // is again returned rather than performed.
    let nothing = stitchwort_core::Value::Ctor(g.find_data("Maybe").unwrap(), 0, Vec::new().into());
    let Obs::Call(op, _) = pending.reply(g, nothing).unwrap() else {
        panic!("then `main` prints");
    };
    let stitchwort_core::Value::Ctor(_, 0, io) = force(g, op).unwrap() else {
        panic!("an operation of `{{IO}}`");
    };
    let stitchwort_core::Value::Ctor(d, c, _) = force(g, io[0].clone()).unwrap() else {
        panic!("an `IO` operation");
    };
    assert_eq!(&*g.data(d).ctors[c].name, "%print");
}

/// Building a recursive call runs nothing: `spin 0` evaluates at once, to a
/// suspended `pfix`. Stepping it enters the body, which requests the next
/// call: one tick, with nothing of that call run yet.
#[test]
fn building_a_partial_computation_runs_nothing() {
    let mut session = load(&printing("spin 0", false));
    let main = main_value(&mut session);
    let g = &session.elab.globals;
    let mut machine = Machine::start(g, main);
    let mut frames = None;
    for _ in 0..1000 {
        match machine.step(g).unwrap() {
            Obs::Later(rest) => machine = rest,
            _ => panic!("`spin` only ticks"),
        }
        // A tail call keeps no frames: the loop runs in constant space
        // (`main`'s own pending work, and `spin`'s `Tie`).
        let now = machine.frames();
        assert_eq!(*frames.get_or_insert(now), now, "frames grew");
    }
    assert!(frames.unwrap() <= 3, "{frames:?}");
}

/// Non-tail recursion keeps its pending callers on the heap: a frame per
/// level, not host stack.
#[test]
fn deep_non_tail_recursion_uses_heap_frames() {
    let mut session = load(&printing("sumTo 100000", false));
    let (events, outcome) = run_traced(&mut session, &[], None);
    assert_eq!(outcome, Outcome::Finished);
    assert_eq!(ticks(&events), 100_000);
    assert_eq!(events.last(), Some(&Event::Print("5000050000".into())));
}

/// Ticks are part of what a program means; the runner's limits aren't. Each
/// stretch between operations and ticks has its own budget, so a long loop
/// of small steps runs whatever the budget; one long step runs out with no
/// tick at all.
#[test]
fn resource_limits_are_per_step_not_per_tick() {
    let mut session = load(&printing("countdown 20000", false));
    session.elab.limits.work = 20_000;
    let (events, outcome) = run_traced(&mut session, &[], None);
    assert_eq!(outcome, Outcome::Finished);
    assert_eq!(ticks(&events), 20_000);

    // One step that does a lot of total work: out of resources, no ticks.
    let mut session = load(&format!(
        "{DEFINITIONS}\n\
         def big : Nat -> Nat\n  \
         | 0 => 0\n  \
         | Succ n => Succ (big n)\n\n\
         def main () : {{IO, Partial}} () := print (Nat.toText (big 1000000 + immediate 1))\n"
    ));
    session.elab.limits.work = 20_000;
    let main = session.main().unwrap();
    let mut trace = Vec::new();
    let result = session.run_main_with(
        &main,
        &mut &b""[..],
        &mut std::io::sink(),
        &Policy::default(),
        &mut |e| trace.push(e),
    );
    assert!(matches!(result, Err(RunError::Resource(_))), "{result:?}");
    assert!(trace.is_empty(), "{trace:?}");
}

/// A partial `main` is run by `simulate` too, as a scripted run of the
/// runner with a tick limit.
#[test]
fn simulate_runs_a_partial_main() {
    let mut session = load(&io_program("echo 0"));
    assert_eq!(
        session.simulate(&["one", "two"]).unwrap(),
        vec!["one", "two", "2"]
    );
    let mut forever = load(&io_program("spin 0"));
    let e = forever.simulate(&[]).unwrap_err();
    assert_eq!(e.code, "E-RESOURCE");
    assert!(e.message.contains("recursive calls"), "{}", e.message);
}

/// The adder reads until the end of its input, however long: 5000 numbers,
/// five times the old bound. The fuelled version stops at 1000, and agrees
/// with it below that.
#[test]
fn the_adder_reads_until_the_end_of_its_input() {
    // `simulate` of the fuelled version writes the input as a list literal,
    // which needs more stack than a test thread's.
    stitchwort_driver::driver::with_stack(64 * 1024 * 1024, adder_reads_until_the_end);
}

fn adder_reads_until_the_end() {
    let read = |name: &str| {
        std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../examples/accept")
                .join(name),
        )
        .unwrap()
    };
    let load = |source: &str| {
        let mut session = Session::for_stack(64 * 1024 * 1024);
        session.load("test.sw", source).unwrap();
        session
    };
    let mut adder = load(&read("adder.sw"));
    let mut fuelled = load(&read("adder-fuel.sw"));
    let numbers: Vec<String> = (1..=5000).map(|n| n.to_string()).collect();
    let mut lines: Vec<&str> = vec!["Ada"];
    lines.extend(numbers.iter().map(String::as_str));
    let printed = adder.simulate(&lines).unwrap();
    assert_eq!(
        printed.last().unwrap(),
        "The sum is 12502500. Goodbye, Ada."
    );
    let cut = fuelled.simulate(&lines).unwrap();
    assert_eq!(cut.last().unwrap(), "The sum is 500500. Goodbye, Ada.");
    // Within the bound, they're the same program.
    for input in [
        &lines[..1],
        &lines[..20],
        &["Ada", "1", "x", "", "5"][..],
        &[][..],
    ] {
        assert_eq!(
            adder.simulate(input).unwrap(),
            fuelled.simulate(input).unwrap(),
            "{input:?}"
        );
    }
}
