//! Tick counts of partial programs on the reference runner (the driver's)
//! and the fast runtime (docs/proposals/partial.md §7.4.3,
//! docs/proposals/partial-tests.md §1.3).
//!
//! A limit of `n` allows exactly `n` ticks: a program that needs `n` ticks
//! finishes under it, and one that needs `n + 1` is inconclusive. So the
//! fewest ticks a run needs is the smallest limit under which it isn't
//! inconclusive. That is found here for both runners, by trying limits in
//! turn, and the two must give the same number, the one the program
//! needs, and the one the reference runner's trace counts. The runners must
//! also end the same way, with the same output, at every limit.
//!
//! The JS runner has no tick limit and no tick counter, so it takes no part.

use std::path::{Path, PathBuf};

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::run::{Event, Outcome as RefOutcome, Policy as RefPolicy, RunError};
use stitchwort_rt::{Limits, Outcome, Policy, lower_main, run_main_with};

const STACK: usize = 256 * 1024 * 1024;

/// How a run ended, the same for both runners.
#[derive(Debug, PartialEq, Eq)]
enum Ended {
    Finished,
    OutOfTicks,
    Failed(String),
}

fn accept(name: &str) -> String {
    let path: PathBuf = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn session(source: &str) -> Session {
    let mut session = Session::for_stack(STACK);
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    session
}

fn ended<T>(result: Result<T, RunError>, finished: impl Fn(T) -> Ended) -> Ended {
    match result {
        Ok(t) => finished(t),
        Err(RunError::Failed(message)) => Ended::Failed(message),
        Err(other) => panic!("{other}"),
    }
}

/// Runs `main` on the reference runner with this limit: how it ended, what
/// it printed, and the ticks in its trace.
fn reference(session: &mut Session, input: &str, limit: u64) -> (Ended, String, usize) {
    let main = session.main().expect("`main` has the right type");
    let mut output = Vec::new();
    let mut ticks = 0;
    let result = session.run_main_with(
        &main,
        &mut input.as_bytes(),
        &mut output,
        &RefPolicy {
            max_ticks: Some(limit),
        },
        &mut |event| ticks += usize::from(event == Event::Tick),
    );
    let ended = ended(result, |outcome| match outcome {
        RefOutcome::Finished => Ended::Finished,
        RefOutcome::OutOfTicks => Ended::OutOfTicks,
    });
    (ended, String::from_utf8(output).expect("text"), ticks)
}

/// The same on the fast runtime.
fn fast(session: &mut Session, input: &str, limit: u64) -> (Ended, String) {
    let main = session.main().expect("`main` has the right type");
    let program = lower_main(
        &session.elab.globals,
        session.elab.limits,
        main.term(),
        main.row,
    )
    .expect("lowers");
    let mut output = Vec::new();
    let result = run_main_with(
        &program,
        Limits::from_core(session.elab.limits),
        &Policy {
            max_ticks: Some(limit),
        },
        &mut input.as_bytes(),
        &mut output,
    );
    let ended = ended(result, |outcome| match outcome {
        Outcome::Finished => Ended::Finished,
        Outcome::OutOfTicks => Ended::OutOfTicks,
    });
    (ended, String::from_utf8(output).expect("text"))
}

/// Checks that `source`, run with `input`, needs `expected` ticks on both
/// runners, and finishes (or fails) the same way at every limit up to there.
fn needs(source: &str, input: &str, expected: u64, end: Ended) {
    let source = source.to_string();
    let input = input.to_string();
    with_stack(STACK, move || {
        let mut session = session(&source);
        for limit in 0..=expected + 1 {
            let (ref_ended, ref_output, ref_ticks) = reference(&mut session, &input, limit);
            let (fast_ended, fast_output) = fast(&mut session, &input, limit);
            assert_eq!(fast_ended, ref_ended, "limit {limit}");
            if limit < expected {
                assert_eq!(ref_ended, Ended::OutOfTicks, "limit {limit}");
                // Stopped on needing tick `limit + 1`: it has had exactly
                // `limit`.
                assert_eq!(ref_ticks as u64, limit, "limit {limit}");
            } else {
                assert_eq!(ref_ended, end, "limit {limit}");
                assert_eq!(ref_ticks as u64, expected, "limit {limit}");
                // Under any limit that lets it finish, the output is the
                // same, and the runners agree on it.
                assert_eq!(fast_output, ref_output, "limit {limit}");
            }
        }
    });
}

const RECURSION: &str = r#"
import Std (IO, Nat)

-- Not a tail call: each level waits for the one below.
def sumTo: Nat -> {Partial} Nat
  | 0 => 0
  | Succ below => Succ below + sumTo below

def isEven: Nat -> {Partial} Bool
  | 0 => True
  | Succ below => isOdd below

def isOdd: Nat -> {Partial} Bool
  | 0 => False
  | Succ below => isEven below

def main(): {IO, Partial} () :=
  IO.print "${sumTo 10} ${isEven 7} ${isEven 10}"
"#;

#[test]
fn collatz_27_takes_111_ticks() {
    needs(&accept("collatz.sw"), "", 111, Ended::Finished);
}

#[test]
fn recursion_that_isnt_a_tail_call_and_mutual_recursion() {
    // `sumTo 10` makes 10 recursive calls, `isEven 7` 7, `isEven 10` 10.
    needs(RECURSION, "", 27, Ended::Finished);
}

/// The message `main` fails with on this input, from an unlimited run.
fn failure(source: &str, input: &str) -> Ended {
    let (source, input) = (source.to_string(), input.to_string());
    let ended = with_stack(STACK, move || {
        reference(&mut session(&source), &input, u64::MAX).0
    });
    assert!(matches!(ended, Ended::Failed(_)), "{ended:?}");
    ended
}

#[test]
fn a_partial_main_that_fails() {
    // `sumLines` runs once for each of the two numbers before the bad line.
    let source = accept("main-fail-partial.sw");
    needs(&source, "1\n2\nx\n", 2, failure(&source, "1\n2\nx\n"));
    needs(&source, "x\n", 0, failure(&source, "x\n"));
}

const MAP_COLLATZ: &str = r#"
import Std (IO, List, Nat)

def collatzSteps (n: Nat): {Partial} Nat :=
  if n <= 1 then 0
  else if n % 2 == 0 then 1 + collatzSteps (n / 2)
  else 1 + collatzSteps (3 * n + 1)

def main(): {IO, Partial} () :=
  IO.print "${List.map [3, 7, 27] collatzSteps}"
"#;

#[test]
fn a_partial_map_adds_no_ticks_of_its_own() {
    // `collatzSteps` takes 7, 16 and 111 steps for 3, 7 and 27: the map
    // itself makes no recursive call (docs/proposals/partial-stage-3.md §4).
    needs(MAP_COLLATZ, "", 7 + 16 + 111, Ended::Finished);
}

#[test]
fn a_partial_main_that_fails_deep_in_recursion() {
    // Each loop makes 5 recursive calls to the bottom, where it fails.
    let source = accept("main-fail-partial-deep.sw");
    for input in ["descend\n5\n", "countdown\n5\n"] {
        needs(&source, input, 5, failure(&source, input));
    }
}

// Handlers around partial code (docs/proposals/partial-handlers.md, lane C):
// lane A's programs, as lane B's trace test runs them on the reference
// runner (`handled_traces_agree_with_the_model` in
// `crates/driver/tests/partial.rs`), with the ticks the model's own tests
// expect. The machine must need the same ticks, and print the same, at
// every limit.

/// Lane A's handled programs, in Stitchwort.
const HANDLER_DEFINITIONS: &str = include_str!("../../driver/tests/partial_handlers.sw");

fn handler_program(body: &str) -> String {
    format!("{HANDLER_DEFINITIONS}\ndef main (): {{IO, Partial}} () :=\n  {body}\n")
}

#[test]
fn handled_programs_need_the_models_ticks() {
    let cases: [(&str, u64); 10] = [
        ("IO.print (showResult (toResult (() => countdown 5)))", 2),
        ("IO.print (showResult (toResult (() => countdown 2)))", 2),
        ("IO.print (showResult (toResult stopThenSpin))", 0),
        (
            "IO.print (Nat.toText (fromLines [\"n\", \"e\", \"s\", \"w\", \"q\"] (() => play 0)))",
            5,
        ),
        ("IO.print (showList (collectIn (() => search 2)))", 6),
        ("IO.print (Nat.toText (walk 2))", 5),
        ("IO.print (Nat.toText (walk 12))", 12 * 13 / 2 + 12),
        (
            "IO.print (showResult (toResult (() => (runCounter 0 (() => climb 0)).fst)))",
            2,
        ),
        (
            "let (result, count) := runCounter 0 (() => toResult (() => climb 0))\n  \
             IO.print (showResult result ++ \" \" ++ Nat.toText count)",
            2,
        ),
        ("IO.print (Nat.toText (answered ()))", 4),
    ];
    for (body, ticks) in cases {
        needs(&handler_program(body), "", ticks, Ended::Finished);
    }
}

/// A handler that resumes twice runs the first branch to its end first: if
/// it never ends, the second never runs (D1256). Both runners stop at the
/// limit, having printed the same.
#[test]
fn a_looping_first_branch_starves_the_second() {
    let source = handler_program("IO.print (showList (collectIn leftLoops))");
    with_stack(STACK, move || {
        let mut session = session(&source);
        for limit in [0, 1, 1000] {
            let (ref_ended, ref_output, ref_ticks) = reference(&mut session, "", limit);
            let (fast_ended, fast_output) = fast(&mut session, "", limit);
            assert_eq!(ref_ended, Ended::OutOfTicks, "limit {limit}");
            assert_eq!(fast_ended, ref_ended, "limit {limit}");
            assert_eq!(ref_ticks as u64, limit, "limit {limit}");
            assert_eq!(fast_output, ref_output, "limit {limit}");
            assert_eq!(fast_output, "left\n", "limit {limit}");
        }
    });
}

#[test]
fn the_partial_handlers_example_needs_the_same_ticks() {
    // `caught 5` and `caught 2` take 2 ticks each, `dropped` none, and the
    // seeded die rolls five times before its six.
    needs(
        &accept("partial-handlers.sw"),
        "",
        2 + 2 + 5,
        Ended::Finished,
    );
}
