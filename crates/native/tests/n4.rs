//! Stage N4 of docs/proposals/native-compilation.md: effects and handlers.
//! Native code builds the effect runtime's values as the machine does
//! (`bind` inline, the other natives run by the machine for it), and the
//! effect loop and the `IO` runner call compiled continuations. Programs
//! with state handlers, exceptions, `Random` under a seeded handler, a
//! handler around partial code (`foldD`), resumptions used more than once,
//! `IO` through the runner, and every `-- run:` line of the effect examples
//! must give what the machine gives (the same effect counts too), make the
//! same allocation trace event for event, stop at the same step and frame
//! limits freeing everything (inside handlers included), and run effect
//! loops in constant stack.

mod common;

use std::cell::RefCell;
use std::path::Path;
use std::rc::Rc;

use common::*;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_native::n1::{Options, factory};
use stitchwort_rt::value::Value;
use stitchwort_rt::{Limits, Machine, MainRow, alloc_trace, lower_main};
use stitchwort_syntax::parse_expression;

/// A state-passing handler (each `bump` a jump of its loop), `Fail` caught
/// as a value, a handler resuming more than once (`Pick`), a generator
/// seeded by a state-passing handler of its own (`Random`, total), the
/// roguelike's `seeded` around partial code (a `foldD`), and `IO` printed in
/// a loop through the runner.
const HANDLERS: &str = r#"import Std (Empty, Fail, IO, List, Nat, Result, Text)

ability Counter where
  bump: () → {Counter} Nat

def Counter.from (init: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | Counter.bump u, k => s => k s (s + 1)
  run init

def countUp: Nat → {Counter} Nat
  | 0 => Counter.bump()
  | Succ n =>
    let here := Counter.bump()
    here + countUp n

ability Pick where
  pick: Nat → {Pick} Nat

def resumeEach (k: Nat → {e} List Nat): Nat → {e} List Nat
  | 0 => []
  | Succ n =>
    let before := resumeEach k n
    let after := k n
    List.append before after

def Pick.all (prog: () → {Pick | e} Nat): {e} List Nat :=
  handle prog() with
    | return x => [x]
    | Pick.pick count, k => resumeEach k count

def picks (counts: List Nat): {Pick} Nat :=
  List.sum (List.map counts (count => Pick.pick count * 10))

def halve (n: Nat): {Fail} Nat :=
  if n % 2 == 1 then Empty.absurd (Fail.stop "odd: ${n}") else n / 2

def showResult: Result (List Nat) Text → Text
  | Ok xs => "Ok ${List.sum xs}"
  | Err msg => "Err " ++ msg

ability Random where
  next: () → {Random} Nat

def lcg (seed: Nat): Nat := (seed * 1103515245 + 12345) % 2147483648

def seededTotal (seed: Nat) (prog: () → {Random | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current =>
        let following := lcg current
        resume (following / 65536) following
  run seed

def seeded (seed: Nat) (prog: () → {Random, Partial | e} a): {Partial | e} a :=
  let run: Nat → {Partial | e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current =>
        let following := lcg current
        resume (following / 65536) following
  run seed

def rolls: Nat → {Random} List Nat
  | 0 => []
  | Succ n =>
    let r := next () % 6
    Cons r (rolls n)

def rollsUntilSix (count: Nat): {Random, Partial} Nat :=
  if next () % 6 == 5 then count + 1 else rollsUntilSix (count + 1)

def report: List Nat → {IO} ()
  | [] => ()
  | Cons x rest =>
    IO.print "roll ${x}"
    report rest

def main(): {IO, Partial} () :=
  IO.print "count: ${Counter.from 5 (() => countUp 20)}"
  IO.print "picks: ${List.sum (Pick.all (() => picks [2, 3, 1]))} of ${List.length (Pick.all (() => picks [2, 3, 1]))}"
  IO.print (showResult (Fail.toResult (() => List.map [4, 8, 12] (n => halve n))))
  IO.print (showResult (Fail.toResult (() => List.map [4, 7, 12] (n => halve n))))
  report (seededTotal 3 (() => rolls 6))
  IO.print "rolls until a six: ${seeded 1 (() => rollsUntilSix 0)}"
"#;

#[test]
fn handlers_agree_with_the_machine() {
    let out = agrees(HANDLERS);
    assert!(out.starts_with("count: "), "{out}");
    assert!(out.contains("Err odd: 7"), "{out}");
    assert!(out.contains("rolls until a six: 6"), "{out}");
    assert_eq!(out.matches("roll ").count(), 6, "{out}");
}

#[test]
fn handler_traces_are_the_same() {
    same_trace(HANDLERS);
}

/// A program whose only function value applied is a `bind`'s continuation
/// (no `Apply` of one argument anywhere): the inline `bind` needs the
/// one-argument slow path all the same (found by `build --native`).
#[test]
fn a_bind_is_the_only_application() {
    let source = "import Std (IO, Nat)\n\n\
                  def countdown: Nat -> {IO} ()\n  \
                    | 0 => IO.print \"go\"\n  \
                    | Succ n =>\n    \
                      IO.print (Nat.toText (Succ n))\n    \
                      countdown n\n\n\
                  def main(): {IO} () := countdown 2\n";
    assert_eq!(agrees(source), "2\n1\ngo\n");
    same_trace(source);
}

/// Small enough to sweep every limit: a state handler, a caught failure, a
/// resumption used twice and the seeded handler around partial code, so
/// that running out of steps or frames happens at every point inside each
/// handler, its clauses and its continuations.
const SMALL_HANDLERS: &str = r#"import Std (Empty, Fail, IO, List, Nat, Result, Text)

ability Counter where
  bump: () → {Counter} Nat

def Counter.from (init: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | Counter.bump u, k => s => k s (s + 1)
  run init

def countUp: Nat → {Counter} Nat
  | 0 => Counter.bump()
  | Succ n =>
    let here := Counter.bump()
    here + countUp n

ability Pick where
  pick: () → {Pick} Nat

def Pick.both (prog: () → {Pick | e} List Nat): {e} List Nat :=
  handle prog() with
    | return x => x
    | Pick.pick u, k => List.append (k 1) (k 2)

def halve (n: Nat): {Fail} Nat :=
  if n % 2 == 1 then Empty.absurd (Fail.stop "odd") else n / 2

ability Random where
  next: () → {Random} Nat

def seeded (seed: Nat) (prog: () → {Random, Partial | e} a): {Partial | e} a :=
  let run: Nat → {Partial | e} a :=
    handle prog() with
      | return result => _ => result
      | next (), resume => current => resume (current % 7) (current + 3)
  run seed

def rollsUntilSix (count: Nat): {Random, Partial} Nat :=
  if next () == 6 then count + 1 else rollsUntilSix (count + 1)

def main(): {IO, Partial} () :=
  IO.print "${Counter.from 1 (() => countUp 1)}"
  IO.print "${List.sum (Pick.both (() => [Pick.pick(), Pick.pick() * 10]))}"
  IO.print "${Fail.orElse 9 (() => halve 4 + halve 3)}"
  IO.print "${seeded 3 (() => rollsUntilSix 0)}"
"#;

#[test]
fn every_error_exit_in_a_handler_frees_everything() {
    with_stack(STACK, || {
        let (program, limits) = lowered(SMALL_HANDLERS);
        let (least_steps, least_frames) = every_limit_agrees(&program, limits);
        assert!(least_steps > 20, "{least_steps}");
        assert!(least_frames > 3, "{least_frames}");
    });
}

/// Effect loops 250,000 long under a frame limit of 100, on a 64 MiB
/// native stack: a state-passing handler's jumps, a fold whose clause
/// resumes in a tail position, and the same with an open row (a lazy
/// resumption, which native code reaches by a tail apply: a tail request).
#[test]
fn effect_loops_run_in_constant_stack() {
    const SMALL: usize = 64 * 1024 * 1024;
    let source = r#"import Std (IO, Nat)

ability Counter where
  bump: () → {Counter} Nat

def Counter.from (init: Nat) (prog: () → {Counter | e} a): {e} a :=
  let run: Nat → {e} a :=
    handle prog() with
      | return x => s => x
      | Counter.bump u, k => s => k s (s + 1)
  run init

def bumps: Nat → Nat → {Counter} Nat
  | 0, acc => acc
  | Succ n, acc => bumps n (acc + Counter.bump() % 2)

ability Env where
  ask: () → {Env} Nat

def Env.give (value: Nat) (prog: () → {Env} a): a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def Env.giveIn (value: Nat) (prog: () → {Env | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def asks: Nat → Nat → {Env} Nat
  | 0, acc => acc
  | Succ n, acc => asks n (acc + Env.ask())

def main(): {IO} () :=
  IO.print "${Counter.from 0 (() => bumps 250000 0)} ${Env.give 3 (() => asks 250000 0)} ${Env.giveIn 2 (() => asks 250000 0)}"
"#;
    with_stack(SMALL, move || {
        let (program, limits) = lowered_for(source, SMALL);
        let limits = Limits {
            frames: 100,
            ..limits
        };
        let machine = on_machine(&program, limits);
        assert_eq!(machine, ("125000 750000 500000\n".to_string(), Ok(())));
        let (native, notes) = native_on(&program, limits, false, SMALL);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(native, machine);
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

/// Every `-- run:` line of the effect examples (the handler shapes of the
/// effect runtime, resumptions stored, resumed many times and through
/// nested handlers and translations, state-passing handlers every way they
/// resume): the expression lowered as an entry, whose value native code
/// computes as the machine does, with the same effect counts and the same
/// allocation trace, freeing every cell.
#[test]
fn effect_examples_agree_with_the_machine() {
    with_stack(STACK, || {
        stitchwort_rt::native_abi::probe_layout().expect("the layout is as expected");
        let mut ran = 0;
        for name in ["effect-runtime.sw", "effect-handlers.sw", "effect-state.sw"] {
            let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../examples/extract")
                .join(name);
            let text = std::fs::read_to_string(&path).expect("readable example");
            let mut session = Session::for_stack(STACK);
            session
                .load(name, &text)
                .unwrap_or_else(|e| panic!("{name} doesn't check: {e:?}"));
            for line in text.lines().filter_map(|l| l.strip_prefix("-- run:")) {
                let source = line.trim();
                let file = session.sources.add("<run>", source);
                let expr = parse_expression(file, source).expect("run line parses");
                let (term, _) = session
                    .elab
                    .infer_expr(&expr)
                    .unwrap_or_else(|d| panic!("`{source}` doesn't check: {}", d.message));
                let g = &session.elab.globals;
                let program = lower_main(g, session.elab.limits, &term, MainRow::Io)
                    .unwrap_or_else(|e| panic!("lowering `{source}`: {e:?}"));
                let limits = Limits::from_core(session.elab.limits);
                // Runs the entry, on the machine or natively (counting
                // through the runtime if `trace`): its value's text, whether
                // it equals the machine's, and the effect counts.
                let run = |native: bool, trace: bool, expected: Option<&Value>| {
                    let mut m = Machine::new(&program, limits);
                    let notes = Rc::new(RefCell::new(Vec::new()));
                    if native {
                        let options = Options {
                            trace_refcounts: trace,
                            stack_size: Some(STACK),
                        };
                        let islands = factory(options, notes.clone())(&program, m.image())
                            .unwrap_or_else(|| panic!("`{source}`: {:#?}", notes.borrow()));
                        m.set_native(islands);
                    }
                    let v = m
                        .entry()
                        .unwrap_or_else(|e| panic!("`{source}` (native: {native}): {e}"));
                    let agrees = expected.is_none_or(|e| same(e, &v));
                    (v, agrees, m.effect_counts())
                };
                // The machine's value to compare with, then a traced run on
                // each, its machine and its value dropped inside the trace.
                let (machine, _, _) = run(false, false, None);
                let traced = |native: bool| {
                    alloc_trace::start();
                    let (v, agrees, counts) = run(native, true, Some(&machine));
                    assert!(
                        agrees,
                        "{name}: `{source}`: native code disagrees with {machine:?}"
                    );
                    drop(v);
                    (alloc_trace::finish(), counts)
                };
                let (on_machine, machine_counts) = traced(false);
                let (natively, native_counts) = traced(true);
                assert_eq!(native_counts, machine_counts, "{name}: `{source}`");
                assert_eq!(natively.leaks(), Vec::<u32>::new(), "{name}: `{source}`");
                let (machine, native) = (on_machine.render(), natively.render());
                if machine != native {
                    let first = machine
                        .lines()
                        .zip(native.lines())
                        .position(|(a, b)| a != b)
                        .unwrap_or(machine.lines().count().min(native.lines().count()));
                    let window = |text: &str| {
                        text.lines()
                            .skip(first.saturating_sub(6))
                            .take(14)
                            .collect::<Vec<_>>()
                            .join(" | ")
                    };
                    panic!(
                        "{name}: `{source}`: the traces differ from event {first}:\n machine {}\n native  {}",
                        window(&machine),
                        window(&native)
                    );
                }
                ran += 1;
            }
        }
        assert!(ran >= 30, "{ran}");
    });
}
