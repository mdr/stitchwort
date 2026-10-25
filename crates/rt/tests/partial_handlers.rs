//! Handlers around partial code on the machine
//! (docs/proposals/partial-handlers.md §5, lane C): stack safety at a
//! million handled operations and a million ticks under a state handler
//! (§5.3), which handlers copy their frames (§5.2), and that capturing and
//! restoring frames leaks no cell (the allocation trace). The traces and
//! ticks against the reference runner are in `tick_counts.rs`.

use std::time::Instant;

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::alloc_trace;
use stitchwort_rt::{Limits, Policy, RouteCounts, lower_main, run_main_counting};

const STACK: usize = 256 * 1024 * 1024;

/// Lane A's handled programs, in Stitchwort.
const HANDLER_DEFINITIONS: &str = include_str!("../../driver/tests/partial_handlers.sw");

/// Loops for the stack tests, under `runCounter` (a state handler).
const LOOPS: &str = r#"
-- A thousand handled operations, in total code.
def bump: Nat → {Counter} ()
  | 0 => ()
  | Succ below =>
    incr ()
    bump below

-- `n` rounds of a thousand handled operations: one tick a round.
def rounds (n: Nat): {Counter, Partial} Nat :=
  if n == 0 then get () else
    bump 1000
    rounds (n - 1)

-- One tick and one handled operation a turn.
def countUp (n: Nat): {Counter, Partial} Nat :=
  if n == 0 then get () else
    incr ()
    countUp (n - 1)
"#;

fn program(body: &str) -> String {
    format!("{HANDLER_DEFINITIONS}\n{LOOPS}\ndef main (): {{IO, Partial}} () :=\n  {body}\n")
}

/// What one run on the machine did.
struct Run {
    output: String,
    counts: RouteCounts,
    seconds: f64,
    leaks: Option<Vec<u32>>,
}

/// Runs `main` of `source` on the machine, with the allocation trace if
/// `trace`.
fn run(source: &str, trace: bool) -> Run {
    let source = source.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", &source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("`main` has the right type");
        let program = lower_main(
            &session.elab.globals,
            session.elab.limits,
            main.term(),
            main.row,
        )
        .expect("lowers");
        let mut output = Vec::new();
        if trace {
            alloc_trace::start();
        }
        let start = Instant::now();
        let (result, counts) = run_main_counting(
            &program,
            Limits::from_core(session.elab.limits),
            &Policy::default(),
            &mut "".as_bytes(),
            &mut output,
        );
        let seconds = start.elapsed().as_secs_f64();
        let leaks = trace.then(|| alloc_trace::finish().leaks());
        result.unwrap_or_else(|e| panic!("{e}"));
        Run {
            output: String::from_utf8(output).expect("text"),
            counts,
            seconds,
            leaks,
        }
    })
}

/// A million handled operations, a thousand at a time between ticks, in
/// constant frames: each operation captures the few frames between it and
/// the handler, and the state handler resumes once, so nothing is copied.
#[test]
fn a_million_handled_operations() {
    let run = run(
        &program("IO.print (Nat.toText (runCounter 0 (() => rounds 1000)).fst)"),
        false,
    );
    assert_eq!(run.output, "1000000\n");
    // `bump`'s million `incr`s and the one `get`.
    assert_eq!(run.counts.captured, 1_000_001);
    assert_eq!(run.counts.copies, 0);
    println!("a million handled operations: {:.3} s", run.seconds);
}

/// A million ticks under a state handler, each turn with a handled
/// operation: the loop's tail calls keep no frame, above or below the
/// handler.
#[test]
fn a_million_ticks_under_a_state_handler() {
    let run = run(
        &program("IO.print (Nat.toText (runCounter 0 (() => countUp 1000000)).fst)"),
        false,
    );
    assert_eq!(run.output, "1000000\n");
    assert_eq!(run.counts.captured, 1_000_001);
    assert_eq!(run.counts.copies, 0);
    println!(
        "a million ticks under a state handler: {:.3} s",
        run.seconds
    );
}

/// Only a resumption called again later copies its frames: `collectIn`
/// around `search 2` forks three times, and each `k True` runs while the
/// clause still holds `k` for `k False` (§5.2). One-shot handlers never
/// copy.
#[test]
fn only_resuming_more_than_once_copies() {
    let cases = [
        ("IO.print (showList (collectIn (() => search 2)))", 3),
        (
            "IO.print (Nat.toText (fromLines [\"n\", \"e\", \"s\", \"w\", \"q\"] (() => play 0)))",
            0,
        ),
        ("IO.print (showResult (toResult (() => countdown 5)))", 0),
        ("IO.print (Nat.toText (walk 12))", 0),
        ("IO.print (Nat.toText (answered ()))", 0),
    ];
    for (body, copies) in cases {
        let run = run(&program(body), false);
        assert_eq!(run.counts.copies, copies, "{body}");
    }
}

/// Capturing, restoring, copying and dropping resumptions frees every cell
/// it allocated: resumed once (`runCounter`, `fromLines`), twice
/// (`collectIn`), never (`toResult` drops `k` and the frames it holds), and
/// handlers nested and inside a recursive function (`walk`).
#[test]
fn capture_and_restore_leak_nothing() {
    for body in [
        "IO.print (Nat.toText (runCounter 0 (() => countUp 100)).fst)",
        "IO.print (Nat.toText (fromLines [\"n\", \"e\", \"s\", \"w\", \"q\"] (() => play 0)))",
        "IO.print (showList (collectIn (() => search 3)))",
        "IO.print (showResult (toResult (() => countdown 5)))",
        "IO.print (showResult (toResult stopThenSpin))",
        "IO.print (Nat.toText (walk 6))",
        "let (result, count) := runCounter 0 (() => toResult (() => climb 0))\n  \
         IO.print (showResult result ++ \" \" ++ Nat.toText count)",
        "IO.print (Nat.toText (answered ()))",
    ] {
        let run = run(&program(body), true);
        assert_eq!(run.leaks, Some(Vec::new()), "{body}");
    }
}
