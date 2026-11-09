//! Borrowed parameters (stage B1 of docs/proposals/borrow-inference.md):
//! a walk over a value its caller keeps takes no references, and a part of
//! it that escapes is counted once, where it escapes. Native code makes the
//! machine's allocation trace (`same_trace`), and the references taken are
//! counted in native code's own trace.

use crate::common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_rt::alloc_trace;

/// `passes` sums of a list `main` keeps, then the first of one of its
/// lists picked `depth` cells in, `lookups` times. (`total` is only ever
/// lent its list: a caller handing it an owned list at its last use would
/// make it own its parameter.)
fn walks(passes: u64, depth: u64, lookups: u64) -> String {
    format!(
        "import Std (IO, List, Nat, Option, Text)

def total (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [x, ..rest] => x + total rest

def sums (xs: List Nat): Nat → Nat
  | Zero => 0
  | Succ more => total xs + sums xs more

def nth (rows: List (List Nat)) (i: Nat): Option (List Nat) :=
  match rows with
    | [] => None
    | [row, ..rest] => if i == 0 then Some row else nth rest (i - 1)

def first (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [x, .._] => x

def picks (rows: List (List Nat)) (i: Nat): Nat → Nat
  | Zero => 0
  | Succ more => (match nth rows i with | Some row => first row | None => 0) + picks rows i more

def main(): {{IO}} () :=
  let xs := List.range 0 100
  let rows := (List.range 0 50).map (i => List.range i (i + 3))
  -- The same text whatever the counts: printing a number takes
  -- references to the runtime's cached `Char` cells, one per digit.
  let sum := sums xs {passes} + picks rows {depth} {lookups} + xs.length + rows.length
  IO.print (if sum > 0 then \"ran\" else \"nothing\")
"
    )
}

/// The references native code takes in a run of `source` (counting through
/// the runtime, so each is in the trace).
fn incs(source: &str) -> usize {
    let source = source.to_string();
    with_stack(STACK, move || {
        let (program, limits) = lowered(&source);
        // Out of the trace: what the first run in a process sets up once.
        let _ = native(&program, limits, true);
        alloc_trace::start();
        let (ran, notes) = native(&program, limits, true);
        let trace = alloc_trace::finish();
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(ran.1, Ok(()));
        trace.count("inc")
    })
}

#[test]
fn borrowed_walks_agree_with_the_machine() {
    same_trace(&walks(3, 20, 3));
}

/// Walking a kept list again and again takes no references.
#[test]
fn a_borrowed_walk_takes_no_references() {
    assert_eq!(incs(&walks(11, 12, 13)), incs(&walks(41, 12, 13)));
}

/// A row found deep in a kept list and returned is counted once, however
/// deep it was: not at every level of the walk.
#[test]
fn an_escaping_part_is_counted_once() {
    let shallow = incs(&walks(11, 12, 13));
    assert_eq!(incs(&walks(11, 42, 13)), shallow);
    assert_eq!(incs(&walks(11, 12, 33)), shallow + 20);
}

/// `pick x x`, with `x` lent and `pick` borrowing its first parameter and
/// owning its second (it rebuilds it in place), in a tail
/// call and a non-tail call: compiles, and native code makes the machine's
/// trace.
#[test]
fn a_lent_value_lent_and_handed_over_in_one_call() {
    same_trace(
        "import Std (IO, List, Nat, Text)

def total (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [x, ..rest] => x + total rest

def pick (a: List Nat) (b: List Nat): List Nat :=
  match b with
    | [] => [total a]
    | [y, ..ys] => if y > 100 then pick a ys else [y + total a, ..ys]

def tail (x: List Nat): List Nat := pick x x

def notTail (x: List Nat): Nat := (pick x x).length + 1

def main(): {IO} () :=
  let xs := List.range 0 5
  IO.print \"${(tail xs).length} ${notTail xs} ${xs.length}\"
",
    );
}

/// Out of steps or frames anywhere in bodies that borrow (at a call, a
/// tail call to a global, a tail application of a function value):
/// native code stops where the machine does and releases exactly what is
/// live, lent registers forgotten, not dropped.
#[test]
fn every_error_exit_in_a_borrowing_body_agrees() {
    with_stack(STACK, || {
        let (program, limits) = lowered(
            "import Std (IO, List, Nat, Text)

def total (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [x, ..rest] => x + total rest

def largest (xs: List Nat): Nat :=
  match xs with
    | [] => 0
    | [x, ..rest] => Nat.max x (largest rest)

def applyTo (xs: List Nat) (f: Nat → Nat): Nat := f (total xs + largest xs)

def main(): {IO} () :=
  let xs := List.range 0 6
  let fs := [(n: Nat) => n + 1, (n: Nat) => n * 2]
  IO.print \"${fs.map (f => applyTo xs f)} ${xs.length}\"
",
        );
        every_limit_agrees(&program, limits);
    });
}
