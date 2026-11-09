//! Compiled handler dispatch (`stitchwort_rt::dispatch`,
//! docs/proposals/compiled-handler-dispatch.md): each handler's step is
//! lowered as one closure that switches on the operation, with the clauses
//! inlined in its arms, and runs as the partial applications did.

use std::rc::Rc;

use stitchwort_core::Term;
use stitchwort_core::term::Icit;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::{Limits, lower_main, run_main};

const STACK: usize = 256 * 1024 * 1024;

/// A dispatch closure's code.
#[derive(Debug)]
struct Dispatch {
    params: u32,
    captures: u32,
    slots: u32,
}

/// What lowering `main` made, and what it printed on the machine.
struct Lowered {
    ir: String,
    dispatches: Vec<Dispatch>,
    output: String,
}

fn lower_and_run(source: &str) -> Lowered {
    let source = source.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        session.use_test_std_cache();
        session
            .load("test.sw", &source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lower_main(
            &session.elab.ev(),
            session.elab.options.limits,
            main.term(),
            main.row,
        )
        .unwrap_or_else(|e| panic!("lowering: {e:?}"));
        let mut output = Vec::new();
        run_main(
            &program,
            Limits::from_core(session.elab.options.limits),
            &mut "".as_bytes(),
            &mut output,
        )
        .unwrap_or_else(|e| panic!("{e}"));
        Lowered {
            ir: program.to_string(),
            dispatches: program
                .lambdas
                .iter()
                .filter(|l| l.dispatch)
                .map(|l| Dispatch {
                    params: l.params,
                    captures: l.captures,
                    slots: l.body.frame,
                })
                .collect(),
            output: String::from_utf8(output).expect("text"),
        }
    })
}

const TICK: &str = r#"import Std (IO, Nat, Text)

ability Tick where
  tick: () → {Tick} ()

def tickLoop (n: Nat) (acc: Nat): {Tick} Nat :=
  match n with
    | Zero => acc
    | Succ m =>
      Tick.tick()
      tickLoop m (acc + 1)

def runTick (p: () → {Tick} a): a :=
  let go: Nat → a :=
    handle p() with
      | return v => s => v
      | Tick.tick u, k => s => k () (s + 1)
  go 0

def main(): {IO} () := IO.print (Nat.toText (runTick (() => tickLoop 5 0)))
"#;

const EIGHT: &str = r#"import Std (IO, Nat, Text)

ability Eight where
  one: () → {Eight} Nat
  two: Nat → {Eight} Nat
  three: Nat → {Eight} Nat
  four: Nat → {Eight} Nat
  five: Nat → {Eight} Nat
  six: Nat → {Eight} Nat
  seven: Nat → {Eight} Nat
  eight: Nat → {Eight} Nat

def useAll (): {Eight, IO} Nat :=
  let a := one ()
  IO.print ("one " ++ Nat.toText a)
  let b := two a
  let c := three b
  let d := four c
  let e := five d
  let f := six e
  let g := seven f
  eight g

def runEight (base: Nat) (step: Nat) (p: () → {Eight, IO} Nat): {IO} Nat :=
  handle p() with
    | return v => v
    | one (), k => k base
    | two n, k =>
      let m := n + step
      let m2 := m * 2
      k (m2 + base)
    | three n, k => k (n + step)
    | four n, k =>
      IO.print "four"
      let m := n * step
      let m2 := m + base
      k (m2 + 1)
    | five n, k => k (n + 1)
    | six n, k => k (n + base)
    | seven n, k => k (n * 2)
    | eight n, k => k (n + step + base)

def main(): {IO} () := IO.print (Nat.toText (runEight 3 4 useAll))
"#;

/// Handlers around code that may not finish: `toResult` is the fold for
/// partial code (`foldD`), `orElse`'s row `{e}` carries a divergence index
/// (`foldCompD`), used at a partial and a total row.
const PARTIAL: &str = r#"import Std (Empty, Fail, IO, Nat, Result, Text)

def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Empty.absurd (Fail.stop "three") else if n == 0 then 0 else countdown (n - 1)

def toResult (prog: () → {Fail, Partial} a): {Partial} Result a Text :=
  handle prog() with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

def orElse (fallback: a) (prog: () → {Fail | e} a): {e} a :=
  handle prog() with
    | return x => x
    | Fail.stop msg, k => fallback

def half (n: Nat): {Fail} Nat := if n == 7 then Empty.absurd (Fail.stop "odd") else n / 2

def showResult: Result Nat Text → Text
  | Ok n => "Ok " ++ Nat.toText n
  | Err msg => "Err " ++ msg

def main(): {IO, Partial} () :=
  IO.print (showResult (toResult (() => countdown 5)))
  IO.print (showResult (toResult (() => countdown 2)))
  IO.print (Nat.toText (orElse 99 (() => countdown 9)))
  IO.print (Nat.toText (orElse 99 (() => half 7)))
  IO.print (Nat.toText (orElse 99 (() => half 8)))
"#;

/// No step is a partial application of `handlePlus` or of an ability's
/// eliminator: neither is called (their definitions are still lowered).
fn no_partial_steps(ir: &str) {
    for name in ["Std.Effect.handlePlus", ".%elim"] {
        let calls = ir
            .lines()
            .filter(|l| l.contains(name) && !l.trim_start().starts_with("fn "))
            .collect::<Vec<_>>();
        assert!(calls.is_empty(), "{name} applied: {calls:#?}\n{ir}");
    }
}

/// A fused state handler's step (the loop gives it `o`, `k`, `jump` and
/// the state) is one closure of four parameters, capturing nothing here.
#[test]
fn a_fused_state_handler_is_one_closure_of_four() {
    let l = lower_and_run(TICK);
    assert_eq!(l.output, "5\n");
    no_partial_steps(&l.ir);
    assert!(
        l.dispatches
            .iter()
            .any(|d| d.params == 4 && d.captures == 0),
        "{:?}\n{}",
        l.dispatches,
        l.ir
    );
}

/// Eight operations, a handler at `{IO}`: one closure of `o` and `k`
/// switching on all eight, with the forward (the `R` arm) inlined too. It
/// captures what the clauses read, `base` and `step`, once each, and its
/// frame is its largest arm's (the arms reuse each other's slots), not the
/// sum of the clauses'.
#[test]
fn eight_operations_are_one_closure() {
    let l = lower_and_run(EIGHT);
    assert_eq!(l.output, "one 3\nfour\n191\n");
    no_partial_steps(&l.ir);
    assert!(
        l.dispatches.iter().all(|d| d.params == 2 && d.slots <= 6),
        "{:?}",
        l.dispatches
    );
    assert!(
        l.dispatches.iter().any(|d| d.captures == 2),
        "{:?}",
        l.dispatches
    );
    // The forward is inlined in the `R` arm: it performs the operation
    // there, with no closure of its own to apply.
    let run = &l.ir[l.ir.find("fn Main.runEight").expect("runEight")..];
    let run = &run[..run.find("\nfn ").unwrap_or(run.len())];
    let forward = &run[run.find("R(o: v2) =>").expect("an R arm")..];
    assert!(
        forward
            .trim_start_matches("R(o: v2) =>")
            .trim_start()
            .starts_with("Call("),
        "{run}"
    );
}

/// The steps given to `foldD` (a handler around partial code) and to
/// `foldCompD` (a row whose divergence is a parameter, with `callD` as
/// the forward) are dispatches too, and run as before at a partial and a
/// total row.
#[test]
fn partial_and_divergence_indexed_folds_dispatch() {
    let l = lower_and_run(PARTIAL);
    assert_eq!(l.output, "Err three\nOk 0\n99\n99\n4\n");
    no_partial_steps(&l.ir);
    assert!(l.ir.contains("%Effect.foldD("), "{}", l.ir);
    assert!(l.ir.contains("Std.Effect.callD("), "{}", l.ir);
    assert!(
        l.dispatches.len() >= 3 && l.dispatches.iter().all(|d| d.params == 2),
        "{:?}",
        l.dispatches
    );
}

/// A clause that isn't a lambda or a variable is bound outside the
/// dispatch, so it's still computed once, when the handler starts, and its
/// arm applies it.
#[test]
fn a_clause_that_isnt_a_lambda_is_bound_outside() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session.use_test_std_cache();
        session
            .load("test.sw", EIGHT)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let g = &session.elab.ev();
        let dispatch = stitchwort_rt::dispatch::Dispatch::new(g).expect("the core has handlePlus");
        let run = g
            .env
            .defs()
            .iter()
            .find(|d| d.path().to_string() == "Main.runEight")
            .expect("runEight");
        let body = run.run_body().expect("a body");
        let (step, _) = body
            .subterms()
            .find(|(t, _)| {
                dispatch
                    .rewrite_term(g, t, false)
                    .is_ok_and(|s| s.is_some())
            })
            .expect("a handler's step");
        let step = step.clone();
        // `handlePlus … (Eight.%elim … c₁ c₂ … c₈) forward` with `c₁`
        // wrapped as `(c => c) c₁`.
        let (head, mut args) = spine(&step);
        let (elim_head, mut elim_args) = spine(&args[args.len() - 2]);
        let first = elim_args.len() - 8;
        elim_args[first] = Term::app(
            Term::Lam("c".into(), Icit::Explicit, Rc::new(Term::Var(0))),
            elim_args[first].clone(),
        );
        let n = args.len();
        args[n - 2] = apply(elim_head, elim_args);
        let wrapped = apply(head, args);
        let rewritten = dispatch
            .rewrite_term(g, &wrapped, false)
            .expect("rewrites")
            .expect("a dispatch");
        assert_eq!(rewritten.bound.len(), 1);
        let Term::Lam(_, _, inner) = &rewritten.closure else {
            panic!("a lambda of o: {:?}", rewritten.closure)
        };
        let Term::Lam(_, _, body) = &**inner else {
            panic!("a lambda of k: {inner:?}")
        };
        // The bound clause, under `o` and `k`.
        assert!(body.mentions(2), "{body:?}");
        let plain = dispatch
            .rewrite_term(g, &step, false)
            .expect("rewrites")
            .expect("a dispatch");
        assert!(plain.bound.is_empty());
    });
}

/// `f a b …` as `f` and its arguments.
fn spine(term: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut head = term;
    loop {
        match head {
            Term::App(f, a, _) => {
                args.push((**a).clone());
                head = f;
            }
            Term::Loc(_, t) => head = t,
            _ => break,
        }
    }
    args.reverse();
    (head.clone(), args)
}

fn apply(head: Term, args: Vec<Term>) -> Term {
    args.into_iter().fold(head, Term::app)
}
