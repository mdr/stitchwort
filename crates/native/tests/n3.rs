//! Stage N3 of docs/proposals/native-compilation.md: closures. Programs
//! that make and apply function values every way the machine does (lambdas
//! capturing several values, partial applications, over- and
//! under-application of unknown functions, tail applies, function values
//! passed between the machine and native code), and the text and integer
//! operations admitted with them, must print what the machine prints, make
//! the same allocation trace event for event, stop at the same step and
//! frame limits freeing everything, and tail-apply in constant stack.

mod common;

use common::*;
use stitchwort_driver::driver::with_stack;
use stitchwort_rt::Limits;

/// `map` and `fold` with lambdas; closures capturing several values (one a
/// list); partial applications of global functions and of closures; an
/// unknown function under-applied (`partials`), over-applied (`pick k`
/// returns a function and is given three arguments), and applied exactly;
/// function values kept in lists.
const CLOSURES: &str = r#"import Std (IO, List)

def add (a: Nat) (b: Nat): Nat := a + b

def scaler (a: Nat) (b: Nat) (xs: List Nat): Nat → Nat :=
  x => a * x + b + List.length xs

def applyAll: List (Nat → Nat) → Nat → Nat
  | [], x => x
  | Cons f rest, x => applyAll rest (f x)

def partials: List (Nat → Nat → Nat) → Nat → List (Nat → Nat)
  | [], x => []
  | Cons f rest, x => Cons (f x) (partials rest x)

def pick (k: Nat): Nat → Nat → Nat :=
  if k <= 1 then add else (a b => a * b + k)

def combine: List Nat → Nat → Nat
  | [], acc => acc
  | Cons k rest, acc => combine rest (pick k acc k % 100000)

def applyThree: List (Nat → Nat → Nat → Nat) → Nat → Nat
  | [], acc => acc
  | Cons f rest, acc => applyThree rest (f acc 2 3 % 100000)

def run (n: Nat): Nat :=
  let xs := List.range n
  let m := n * 3
  let several: Nat → Nat := x => x * n + m + List.length xs
  let fs := [scaler 2 3 xs, add 7, several, x => x + n, scaler n 1 [1, 2]]
  let gs := partials [add, (a b => a * b + n), pick 5] 3
  let mapped := List.map xs (x => applyAll fs x)
  let folded := List.foldLeft mapped 0 (acc x => acc + x % 1000)
  let threes := [pick, (a => b => c => a + b * c + m), (a b => c => a * c + b), (a b c => a + b + c)]
  folded + applyAll gs n + combine xs 1 + applyThree threes 1 + List.foldLeft (List.map xs several) 0 add

def main(): {IO} () :=
  IO.print "${run 60}"
"#;

/// Continuations: each a closure (or a partial application, or an
/// over-application) that applies the one before in tail position, so
/// running the last runs them all as tail applies. The entry makes the
/// first continuations, so they cross from the machine into native code.
const TAILS: &str = r#"import Std (IO, List)

def countdown: Nat → (Nat → Nat) → Nat
  | Zero, k => k 0
  | Succ n, k => countdown n (x => k (x + 1))

def bump (k: Nat → Nat) (x: Nat): Nat := k (x + 2)

def countdownP: Nat → (Nat → Nat) → Nat
  | Zero, k => k 0
  | Succ n, k => countdownP n (bump k)

def step (k: Nat → Nat → Nat) (x: Nat): Nat → Nat :=
  if x <= 0 then (y => k x y) else (y => k (x + 3) y)

def countdownO: Nat → (Nat → Nat → Nat) → Nat
  | Zero, k => k 1 0
  | Succ n, k => countdownO n (step k)

def run (n: Nat): Nat :=
  countdown n (x => x) + countdownP n (x => x) + countdownO n (a b => a + b)

def main(): {IO} () :=
  IO.print "${run COUNT}"
"#;

fn tails(count: u64) -> String {
    TAILS.replace("COUNT", &count.to_string())
}

/// The text and integer operations the machine computes without frames
/// (the standalone note's "cheap find"), and the `Int` match instructions,
/// with big integers.
const TEXT_AND_INTS: &str = r#"import Std (IO, List, Text, Int)

def sign: Int → Text
  | OfNat Zero => "zero"
  | OfNat (Succ n) => "+${n + 1}"
  | NegSucc n => "-${n + 1}"

def describe: List Int → Text
  | [] => "."
  | Cons i rest => sign i ++ " " ++ describe rest

def ints (n: Nat): List Int := List.map (List.range n) (k => Int.OfNat (k * 7) - Int.OfNat (k * k))

def words (t: Text): Nat := List.length (Text.lines t) + List.length (Text.toList t)

def bigInt (n: Nat): Int := Int.OfNat n * Int.OfNat n * Int.OfNat n * Int.OfNat n * Int.OfNat n - Int.OfNat 7

def run (n: Nat): Text :=
  let xs := ints n
  let less := List.filter xs (i => i < Int.OfNat 3)
  describe xs ++ sign (bigInt 100000) ++ sign (Int.OfNat 0 - bigInt 100000) ++ " ${words "a\nbb\nccc"} ${List.length less}"

def main(): {IO} () :=
  IO.print (run 12)
"#;

#[test]
fn closures_agree_with_the_machine() {
    assert_eq!(agrees(CLOSURES), "202471\n");
    assert_eq!(agrees(&tails(1000)), "6001\n");
    let text = agrees(TEXT_AND_INTS);
    assert!(
        text.starts_with("zero +6 +10 +12 +12 +10 +6 zero -8 -18 -30 -44 .+99999"),
        "{text}"
    );
}

#[test]
fn closure_traces_are_the_same() {
    same_trace(CLOSURES);
    same_trace(&tails(300));
    same_trace(TEXT_AND_INTS);
}

/// Function values cross both ways: the entry makes closures and partial
/// applications that a native root applies, and a native root returns a
/// closure that the machine applies.
#[test]
fn function_values_cross_between_the_machine_and_native_code() {
    let source = r#"import Std (IO, List)

def add (a: Nat) (b: Nat): Nat := a + b

def applyAll: List (Nat → Nat) → Nat → Nat
  | [], x => x
  | Cons f rest, x => applyAll rest (f x)

def makeAdder (k: Nat): Nat → Nat := if k <= 0 then (x => x) else (x => x + k)

def main(): {IO} () :=
  IO.print "${applyAll [n => n + 3, add 4, makeAdder 5] 4} ${(makeAdder 6) 7}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let machine = on_machine(&program, limits);
        let (native, notes) = native(&program, limits, false);
        assert_eq!(native, machine);
        assert_eq!(machine.0, "16 13\n");
        assert!(ran_natively(&notes), "{notes:#?}");
        assert!(
            !notes.iter().any(|n| n.contains("ran on the machine")),
            "{notes:#?}"
        );
    });
    same_trace(source);
}

/// Tail applies of closures, of partial applications and of
/// over-applications run in constant stack: 1,000,000 of each under a
/// frame limit of 100, on a native stack small enough (64 MiB) that a
/// native frame per apply would reach its safety margin.
#[test]
fn tail_applies_run_in_constant_stack() {
    const SMALL: usize = 64 * 1024 * 1024;
    let source = tails(1_000_000);
    with_stack(SMALL, move || {
        let (program, limits) = lowered_for(&source, SMALL);
        let limits = Limits {
            frames: 100,
            ..limits
        };
        let machine = on_machine(&program, limits);
        assert_eq!(machine, ("6000001\n".to_string(), Ok(())));
        let (native, notes) = native_on(&program, limits, false, SMALL);
        assert!(ran_natively(&notes), "{notes:#?}");
        assert_eq!(native, machine);
    });
}

/// Closures, partial applications and over-applications live across
/// calls, applies and tail applies: under every step limit and every frame
/// limit up to the least that finishes, native code stops where the machine
/// does and frees every cell, those the closures hold included.
#[test]
fn every_error_exit_frees_the_live_closures() {
    let source = r#"import Std (IO, List)

def add (a: Nat) (b: Nat): Nat := a + b

def pick (k: Nat): Nat → Nat → Nat :=
  if k <= 1 then add else (a b => a * b + k)

def total: List Nat → Nat
  | [] => 0
  | Cons x rest => x + total rest

def bump (k: Nat → Nat) (x: Nat): Nat := k (x + 2)

def countdown: Nat → (Nat → Nat) → Nat
  | Zero, k => k 0
  | Succ n, k => countdown n (bump (x => k (x + 1)))

def keep: Nat → List Nat → Nat
  | Zero, xs => total xs
  | Succ n, xs =>
    let ys := [n, n + 1]
    let f: Nat → Nat := x => x + total xs + total ys
    let a := keep n ys
    let b := pick n a 2
    a + b + f 1 + countdown 2 (y => y + total ys)

def run (n: Nat): Nat := keep n [1, 2, 3]

def main(): {IO} () :=
  IO.print "${run 3}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        let (least_steps, least_frames) = every_limit_agrees(&program, limits);
        assert!(least_steps > 20, "{least_steps}");
        assert!(least_frames > 5, "{least_frames}");
    });
}
