//! The machine (docs/proposals/fast-runtime.md, stage 2): its differential
//! cases against the reference evaluator (`differential.rs`, shared with
//! the native backend's copy), the outcomes of the library's `test`s on the
//! machine, and what only the machine does: step and frame counts, deep
//! recursion, long lists and reuse.

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::{Limits, Program};

use crate::differential::*;

differential_tests!();

fn machine(program: &Program, limits: Limits, input: &[u8]) -> Run {
    let mut output = Vec::new();
    let result = stitchwort_rt::run_main(program, limits, &mut &input[..], &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}

/// The library's own tests (many of them of the text and integer natives)
/// have the same outcomes on the machine.
#[test]
fn library_tests_agree() {
    with_stack(STACK, || {
        let session = Session::with_library_tests();
        let program = everything(&session, "the library");
        let ran = run_tests(&session, &program, "the library", true);
        eprintln!("{ran} library tests agree");
        assert!(ran >= 70, "{ran}");
    });
}
/// A small program's `main`, on the machine only (for what the reference
/// evaluator takes too long over).
fn on_the_machine(source: &str, limits: Limits) -> Run {
    on_the_machine_with(source, limits, b"")
}

/// A small program's `main`, on the machine only, with `input`.
fn on_the_machine_with(source: &str, limits: Limits, input: &[u8]) -> Run {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        machine(&program, limits, input)
    })
}

/// A list of a million numbers, built and searched by non-tail recursion
/// (a sum would be a loop, `stitchwort_rt::sums`): a million frames deep,
/// on the machine's own stack, then freed.
#[test]
fn deep_recursion_over_a_long_list() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def build: Nat -> List Nat
  | 0 => []
  | Succ n => Cons (n + 1) (build n)

def largest: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => Nat.max x (largest rest)

def main(): {IO} () := IO.print (Nat.toText (largest (build 1000000)))
"#,
        Limits::default(),
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "1000000\n");
}

/// Recursing more deeply than the frame limit allows is `E-RESOURCE`, not a
/// crash. (A product, not a sum, which would be a loop:
/// `stitchwort_rt::sums`.)
#[test]
fn recursing_too_deeply_runs_out() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def count: Nat -> Nat
  | 0 => 0
  | Succ n => 2 * count n

def main(): {IO} () :=
  IO.print "before"
  IO.print (Nat.toText (count 100000))
"#,
        Limits {
            steps: u64::MAX,
            frames: 10_000,
            native_frames: 10_000,
            number_words: false,
        },
    );
    assert_eq!(out, "before\n");
    assert_eq!(
        result,
        Err("ran out of resources: it recursed more deeply than allowed".into())
    );
}

/// With `number_words` (the counterexample search's, SW-907), an operation
/// on a big number costs a step per word: squaring 2 twenty times, 20
/// frames, would make a number of 2^20 bits, but runs out of steps first.
/// Without it, the same steps are plenty.
#[test]
fn big_numbers_cost_their_words_when_they_count() {
    let source = r#"
import Std (Nat, Text)

def square: Nat -> Nat -> Nat
  | 0, n => n
  | Succ k, n => square k (n * n)

def main(): {IO} () := IO.print (Nat.toText (square 20 2 % 1000))
"#;
    let limits = |number_words| Limits {
        steps: 10_000,
        frames: 100,
        native_frames: 100,
        number_words,
    };
    let (out, result) = on_the_machine(source, limits(false));
    assert_eq!(result, Ok(()));
    assert_eq!(out, "136\n");
    let (out, result) = on_the_machine(source, limits(true));
    assert_eq!(out, "");
    assert_eq!(
        result,
        Err("ran out of resources: it took more evaluation steps than allowed".into())
    );
}

/// A loop in tail position runs in constant space, however long.
#[test]
fn tail_calls_dont_grow_the_stack() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def loop: Nat -> Nat -> Nat
  | 0, acc => acc
  | Succ n, acc => loop n (acc + 2)

def main(): {IO} () := IO.print (Nat.toText (loop 3000000 0))
"#,
        Limits {
            steps: u64::MAX,
            frames: 100,
            native_frames: 100,
            number_words: false,
        },
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "6000000\n");
}

/// A function that adds to a call of itself runs as a loop carrying the
/// sum (`stitchwort_rt::sums`): 100,000 elements in 100 frames.
#[test]
fn calls_plus_a_number_dont_grow_the_stack() {
    let source = r#"
import Std (Int, List, Nat, Text)

def size: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => Succ (size rest)

def total: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => x + total rest

def signed: List Nat -> Int
  | [] => -7
  | [x, ..rest] => signed rest + (Nat.toInt x - 3)

def build: Nat -> List Nat -> List Nat
  | 0, acc => acc
  | Succ n, acc => build n (Cons n acc)

def main(): {IO} () :=
  let xs := build 100000 []
  IO.print (Text.join [Nat.toText (size xs), Nat.toText (total xs), Int.toText (signed xs)] ' ')
"#;
    let (out, result) = on_the_machine(
        source,
        Limits {
            steps: u64::MAX,
            frames: 100,
            native_frames: 100,
            number_words: false,
        },
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "100000 4999950000 4999649993\n");
}

/// `List.length` runs as a loop (`List.lengthOnto`), so a list longer than
/// the frame limit has a length.
#[test]
fn list_length_doesnt_grow_the_stack() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def build: Nat -> List Nat -> List Nat
  | 0, acc => acc
  | Succ n, acc => build n (Cons n acc)

def main(): {IO} () := IO.print (Nat.toText (build 100000 []).length)
"#,
        Limits {
            steps: u64::MAX,
            frames: 100,
            native_frames: 100,
            number_words: false,
        },
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "100000\n");
}

/// The list functions that build their result around a call to themselves
/// (`map`, `filter`, `append`, `concat` and `flatMap` through it, `zip`,
/// `take`, `range`) run as loops, so a list
/// longer than the default frame limit (2,000,000) goes through each.
#[test]
fn list_builders_dont_grow_the_stack() {
    let (out, result) = on_the_machine(
        r#"
import Std (List, Nat, Text)

def count (xs: List a): Nat := xs.length

def mapped (xs: List Nat): List Nat := xs.map (x => x + 1)
def kept (xs: List Nat): List Nat := xs.filter (x => x % 3 != 0)
def joined (xs: List Nat): List Nat := xs ++ xs
def single (x: Nat): List Nat := [x, x]
def flat (xs: List Nat): List Nat := xs.flatMap single
def wrapped (xs: List Nat): List (List Nat) := xs.map single
def concatenated (xss: List (List Nat)): List Nat := List.concat xss
def zipped (xs: List Nat): List (Pair Nat Nat) := List.zip xs xs
def taken (xs: List Nat): List Nat := xs.take 2500000

def main(): {IO} () :=
  let xs := List.range 0 3000000
  IO.print (Text.join [
    Nat.toText (count xs),
    Nat.toText (count (mapped xs)),
    Nat.toText (count (kept xs)),
    Nat.toText (count (joined xs)),
    Nat.toText (count (flat xs)),
    Nat.toText (count (concatenated (wrapped xs))),
    Nat.toText (count (zipped xs)),
    Nat.toText (count (taken xs))
  ] ' ')
"#,
        Limits {
            steps: u64::MAX,
            frames: Limits::default().frames,
            native_frames: Limits::default().frames,
            number_words: false,
        },
    );
    assert_eq!(result, Ok(()));
    assert_eq!(
        out,
        "3000000 3000000 2000000 6000000 6000000 6000000 3000000 2500000\n"
    );
}

/// A `let` used in a `match` arm inside a lambda is computed once, as a
/// closure's capture would be, not once per call of the lambda: the helper
/// the `match` is lifted to takes its value. Counted in steps: twenty
/// computations of `slow` would take far more than the limit.
#[test]
fn a_let_in_a_lifted_match_is_computed_once() {
    let (out, result) = on_the_machine(
        r#"
import Std (List, Nat, Text)

def slow (n: Nat): Nat := List.range 0 n |> .sumBy (i => i % 7)

def total (n: Nat) (flag: Option Nat): Nat :=
  let big := slow n
  List.range 0 20 |> .sumBy (i =>
    match flag with
      | Some first => big + i + first
      | None => 0)

def main(): {IO} () := IO.print (Nat.toText (total 20000 (Some 1)))
"#,
        Limits {
            steps: 500_000,
            frames: 1_000_000,
            native_frames: 1_000_000,
            number_words: false,
        },
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "1200150\n");
}

/// On a million characters, each of `Text.take`, `Text.drop` and
/// `Text.contains` is one native step, not one step per character as its
/// definition would be.
#[test]
fn text_take_drop_and_contains_are_native() {
    let input = "\u{1F600}".repeat(999_999) + "b";
    let (out, result) = on_the_machine_with(
        r#"
import Std (Nat, Text, IO)

def main(): {IO} () :=
  let input := IO.readAll()
  let rest := Text.drop input 500000
  IO.print (Nat.toText (Text.length (Text.take rest 250000)))
  IO.print (Nat.toText (Text.length rest))
  IO.print (if Text.contains input "\u{1F600}b" then "found" else "missing")
  IO.print (if Text.contains input "ba" then "found" else "missing")
"#,
        Limits {
            steps: 10_000,
            frames: 100,
            native_frames: 100,
            number_words: false,
        },
        input.as_bytes(),
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "250000\n500000\nfound\nmissing\n");
}

/// `Parse.many` is linear in what it reads: 20,000 digits (AoC 2024 day
/// 9's input) take a few steps each. Its end value was once computed every
/// round, quadratic: about 2×10⁸ steps here (SW-1055; 0.6 s to 12 s on the
/// day's input, and 21 GB on the reference evaluator).
#[test]
fn many_is_linear_in_what_it_reads() {
    let input = "12345".repeat(4_000) + "\n";
    let (out, result) = on_the_machine_with(
        r#"
import Std (Fail, IO, List, Nat, Parse, Text)
import Std.Parse (digit, many1)

def main(): {IO, Fail} () :=
  let digits := Parse.all IO.readAll() (() => many1 (() => digit().toNat))
  IO.print (Nat.toText digits.length)
"#,
        Limits {
            steps: 20_000_000,
            frames: 1_000_000,
            native_frames: 1_000_000,
            number_words: false,
        },
        input.as_bytes(),
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "20000\n");
}

/// `map` builds each new cell in the one it takes apart, when that one is
/// uniquely owned: its code (the loop of the empty-row variant, for a pure callback)
/// reuses the cell.
#[test]
fn map_reuses_its_cells() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "test.sw",
                "import Std (Nat, Text, List)\n\
                 def main(): {IO} () := IO.print (Text.join ((List.range 0 3).map Nat.toText) ',')\n",
            )
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let image = stitchwort_rt::code::compile(&program);
        let map = program
            .globals
            .iter()
            .position(|g| &*g.name == "Std.List.map[empty][cells]")
            .expect("map is used");
        let code = &image.codes[image.global_code[map].expect("map has code") as usize];
        assert!(
            code.instrs
                .iter()
                .any(|i| matches!(i, stitchwort_rt::code::Instr::CtorReuse { .. })),
            "{:?}",
            code.instrs
        );
    });
}

/// A call's arguments read for the last time are moved in, even when a
/// later argument binds the same slot for its own variable: here `a` and `c`
/// share a slot, and each `total` call is the last read of its list
/// (SW-2388: `a` was copied, so the list passed on had a count of 2 and
/// couldn't be reused in place).
#[test]
fn arguments_are_moved_past_siblings_sharing_slots() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "test.sw",
                "import Std (Nat, Text, List)\n\
                 def total (xs: List Nat) (ys: List Nat): Nat :=\n\
                 \x20 match xs with\n\
                 \x20   | [] => ys.length\n\
                 \x20   | [x, ..rest] => x + total rest ys\n\
                 def step (n: Nat) (m: Nat): Nat :=\n\
                 \x20 (let a := List.range 0 n; total a (a.map (x => x + m)))\n\
                 \x20   * (let c := List.range 0 m; total c (c.map (x => x + n)))\n\
                 def main(): {IO} () := IO.print (Nat.toText (step 3 4))\n",
            )
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let image = stitchwort_rt::code::compile(&program);
        let global = |name: &str| {
            program
                .globals
                .iter()
                .position(|g| &*g.name == name)
                .unwrap_or_else(|| panic!("{name} is used"))
        };
        let total = u32::try_from(global("Main.total")).expect("fits");
        let step = global("Main.step");
        let code = &image.codes[image.global_code[step].expect("step has code") as usize];
        let calls: Vec<_> = code
            .instrs
            .iter()
            .filter_map(|i| match i {
                stitchwort_rt::code::Instr::Call { g, args, .. }
                | stitchwort_rt::code::Instr::TailCall { g, args }
                    if *g == total =>
                {
                    Some(*args)
                }
                _ => None,
            })
            .collect();
        assert_eq!(calls.len(), 2, "{:?}", code.instrs);
        for args in calls {
            let ops = &code.ops[args.start as usize..(args.start + args.len) as usize];
            assert!(
                ops.iter().all(|r| r & stitchwort_rt::code::MOVE != 0),
                "copied: {ops:?} in {:?}",
                code.instrs
            );
        }
    });
}

/// `total` walks a list it borrows (no counting), and `twice` (inlined into
/// `check`, which makes the list) lends it its list before matching on it. The run is right as compiled; with the
/// call made to hand over `twice`'s only reference instead of lending it
/// (as a wrong inference or rewrite would), the machine's check, which
/// native code relies on, catches the walk outliving its owner.
#[test]
fn the_machine_catches_a_loan_outliving_its_owner() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use stitchwort_rt::code::{Instr, MOVE};
    use stitchwort_rt::ir::GlobalId;
    use stitchwort_rt::value::Value;
    let source = "import Std (Nat, Text, List)\n\
                  def total (xs: List Nat): Nat :=\n\
                  \x20 match xs with\n\
                  \x20   | [] => 0\n\
                  \x20   | [x, ..rest] => x + total rest\n\
                  def twice (xs: List Nat): Nat :=\n\
                  \x20 total xs + (match xs with | [] => 0 | _ => 1)\n\
                  def check (n: Nat): Nat := twice (List.range 0 n)\n\
                  def main(): {IO} () := IO.print (Nat.toText (check 5))\n";
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let limits = Limits::from_core(session.elab.options.limits);
        let global = |name: &str| {
            program
                .globals
                .iter()
                .position(|g| &*g.name == name)
                .unwrap_or_else(|| panic!("{name} is used"))
        };
        let (total, check) = (global("Main.total"), global("Main.check"));
        let run = |tamper: bool| {
            let mut image = stitchwort_rt::code::compile(&program);
            let code_of = |g: usize| image.global_code[g].expect("has code") as usize;
            assert!(image.codes[code_of(total)].borrows(0), "total borrows");
            if tamper {
                let code = code_of(check);
                let code = &mut image.codes[code];
                let args = code
                    .instrs
                    .iter()
                    .find_map(|i| match i {
                        Instr::Call { g, args, .. } if *g as usize == total => Some(*args),
                        _ => None,
                    })
                    .expect("check calls total");
                code.ops[args.start as usize] |= MOVE;
            }
            let mut m = stitchwort_rt::Machine::with_image(&program, image, limits);
            let f = m.global(GlobalId(check as u32)).expect("check");
            match m.call(f, [Value::Nat(5)]).expect("runs") {
                Value::Nat(n) => n,
                other => panic!("{other:?}"),
            }
        };
        assert_eq!(run(false), 11);
        let caught = catch_unwind(AssertUnwindSafe(|| run(true))).expect_err("caught");
        let message = caught
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| caught.downcast_ref::<&str>().copied())
            .unwrap_or_default();
        assert!(
            message.contains("a borrowed value outlived its owner"),
            "{message}"
        );
    });
}

/// Out of frames deep in a recursive walk over a list it borrows (the
/// caller keeps it), at the default frame limit: the error exit forgets
/// each frame's loan from one table per body, so it is reported promptly
/// (it was a pass over the body per frame, two million of them).
#[test]
fn running_out_of_frames_in_a_borrowing_walk_is_prompt() {
    let started = std::time::Instant::now();
    let (out, result) = on_the_machine(
        r#"
import Std (List, Nat, Text)

def build: Nat -> List Nat
  | 0 => []
  | Succ n => Cons (n + 1) (build n)

def largest (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [x, ..rest] => Nat.max x (largest rest)

def walk (xs: List Nat): Nat := largest xs + xs.length

def main(): {IO} () :=
  IO.print "before"
  IO.print (Nat.toText (walk (build 2100000)))
"#,
        Limits::default(),
    );
    let took = started.elapsed();
    assert_eq!(out, "before\n");
    assert_eq!(
        result,
        Err("ran out of resources: it recursed more deeply than allowed".into())
    );
    eprintln!("ran out of frames and released them in {took:?}");
    assert!(took.as_secs() < 20, "{took:?}");
}
