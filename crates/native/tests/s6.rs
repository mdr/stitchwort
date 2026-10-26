//! Stage S6 of docs/proposals/standalone-executables.md: every pure
//! primitive through the runtime. Programs using each family of pure
//! primitives (`Nat` division and remainder, `Int`, `Float`, `Text`,
//! `Delay` values) must print what the machine prints, make the same
//! allocation trace event for event, and stop at the same step and frame
//! limits, with the edge cases: numbers beyond a machine word, division by
//! zero as the machine has it (`Nat.divFuel` returns its fuel), empty text.

mod common;

use common::*;
use stitchwort_driver::driver::with_stack;

/// `Nat` division and remainder: words on the inline path, numbers beyond a
/// word on the runtime's, and `Nat.divFuel` with a divisor of 0 (which has no
/// proof obligation, unlike `/`).
const NAT_DIVISION: &str = r#"import Std (IO, List, Nat)

def big: Nat := 100000000000 * 100000000000 * 1000 + 12345

def cases: List (Pair Nat Nat) :=
  [MkPair 0 1, MkPair 7 2, MkPair 7 7, MkPair 6 7, MkPair 18446744073709551615 3,
   MkPair 18446744073709551615 18446744073709551615, MkPair 100 1, MkPair big 7,
   MkPair 5 big, MkPair big big, MkPair big 1000000007, MkPair 1000 18446744073709551616]

def divide: Pair Nat Nat → Nat
  | MkPair n d => Nat.divFuel n n (d + 1) + Nat.divFuel n n 0 + Nat.divFuel 3 n (d + 1) + Nat.divFuel 0 n d

def quotients: List (Pair Nat Nat) → Text
  | [] => "."
  | Cons (MkPair n d) rest => "${n / (d + 1)}:${n % (d + 1)};${divide (MkPair n d)} " ++ quotients rest

def run (n: Nat): Text :=
  quotients cases ++ "${List.foldLeft (List.range n) 0 (acc k => acc + (k * 31 + 7) % 13 + (k * 31 + 7) / 13)}"

def main(): {IO} () :=
  IO.print (run 200)
"#;

/// `Int`: matches, comparisons, negation, subtraction of mixed sizes, big
/// values, division and remainder of every sign, `Int.toText`.
const INTS: &str = r#"import Std (IO, List, Text, Int)

def values: List Int :=
  [Int.OfNat 0, Int.OfNat 1, Int.OfNat 9223372036854775807, Int.OfNat 9223372036854775808,
   Int.OfNat 0 - Int.OfNat 1, Int.OfNat 0 - Int.OfNat 9223372036854775808,
   Int.OfNat 0 - Int.OfNat 9223372036854775809, Int.OfNat 100000000000 * Int.OfNat 100000000000 * Int.OfNat 100000000000,
   Int.OfNat 7 - Int.OfNat 100]

def show: List Int → Text
  | [] => "."
  | Cons i rest => Int.toText i ++ " " ++ show rest

def pairs: List Int → List Int → List (Pair Int Int)
  | [], ys => []
  | Cons x xs, ys => List.append (List.map ys (y => MkPair x y)) (pairs xs ys)

def compare: Pair Int Int → Text
  | MkPair x y => (if x < y then "<" else if x == y then "=" else ">") ++ (if x <= y then "l" else "g")

def arithmetic: Pair Int Int → Text
  | MkPair x y => Int.toText (x + y) ++ "," ++ Int.toText (x - y) ++ "," ++ Int.toText (x * y)

def quotient: Pair Int Int → Text
  | MkPair x y =>
    if h: y ≠ Int.OfNat 0 then Int.toText (Int.tdiv x y) ++ "," ++ Int.toText (Int.fdiv x y) ++ "," ++ Int.toText (x / y) ++ "," ++ Int.toText (x % y) ++ "," ++ Int.toText (Int.abs x)
    else "0"

def main(): {IO} () :=
  let ps := pairs values values
  IO.print (show values ++ Text.join (List.map ps compare) ' ' ++ Text.join (List.map ps arithmetic) ' ' ++ Text.join (List.map ps quotient) ' ')
"#;

/// `Float`: arithmetic, rounding, `NaN` and infinities, conversions from
/// `Nat` and `Int`, and `Float.toText`.
const FLOATS: &str = r#"import Std (IO, List, Text, Float, Int)

def values: List Float :=
  [Float.ofNat 0, Float.ofNat 1, Float.ofNat 3, Float.ofInt (Int.OfNat 0 - Int.OfNat 7),
   Float.div (Float.ofNat 1) (Float.ofNat 3), Float.nan, Float.infinity,
   Float.ofNat 100000000000000000000000]

def combine (x: Float): List Float → List Text
  | [] => []
  | Cons y rest =>
    let q := Float.div x y
    List.append [Float.toText (Float.add x y), Float.toText (Float.sub x y), Float.toText (Float.mul x y), Float.toText q, Float.toText (Float.floor q), Float.toText (Float.round q), Float.toText (Float.rem x y)] (combine x rest)

def all: List Float → List Text
  | [] => []
  | Cons x rest => List.append (combine x values) (all rest)

def main(): {IO} () :=
  IO.print (Text.join (all values) ' ')
"#;

/// `Text`: append, length, emptiness, comparison and equality, trimming,
/// taking and dropping, splitting and joining, `Nat` to text and back,
/// characters and back, with empty texts and multi-byte characters.
const TEXTS: &str = r#"import Std (IO, List, Text, Option, Nat)

def texts: List Text := ["", " ", "abc", "  padded  ", "a,b,,c", "héllo wörld", "日本語", "12345", "007", "abc123", "line1\nline2\n\nline4", "98765432109876543210987654321"]

def each (t: Text): Text :=
  let a := "[" ++ t ++ "|${Text.length t}|${Text.isEmpty t}|${Text.trim t}|${Text.take t 2}|${Text.drop t 2}|${Text.take t 100}|${Text.drop t 100}|"
  let b := "${List.length (Text.split t ',')}|${List.length (Text.lines t)}|${Text.contains t "b"}|${Text.contains t ""}|"
  let c := "${Text.toNat t}|${List.length (Text.toList t)}|${Text.fromList (List.reverse (Text.toList t))}|${Text.join (Text.split t ',') ';'}]"
  a ++ b ++ c

def pairwise (a: Text): List Text → List Text
  | [] => []
  | Cons b rest => Cons "${a == b}${Text.less a b}${Text.less b a}${Nat.toText (Text.length (a ++ b))}" (pairwise a rest)

def run: List Text → List Text
  | [] => []
  | Cons t rest => Cons (each t) (List.append (pairwise t texts) (run rest))

def main(): {IO} () :=
  IO.print (Text.join (run texts) ' ')
"#;

/// `Delay` values built by the constructors and kept in data without being
/// run (`Effect.now`, `Effect.lift`, `Effect.bindD`).
const DELAYS: &str = r#"import Std (IO, List, Empty, Effect)
import Std.Effect (Delay)

def later (n: Nat): Delay Empty (e => Empty) Nat := Effect.now n

def chained (n: Nat): Delay Empty (e => Empty) Nat := Effect.bindD (later n) (m => later (m + 1))

def count: List (Delay Empty (e => Empty) Nat) → Nat
  | [] => 0
  | Cons d rest => 1 + count rest

def total (n: Nat): Nat := count (List.map (List.range n) chained)

def main(): {IO} () :=
  IO.print "${total 20}"
"#;

#[test]
fn nat_division_agrees() {
    let text = agrees(NAT_DIVISION);
    assert!(text.starts_with("0:0;"), "{text}");
    same_trace(NAT_DIVISION);
}

#[test]
fn ints_agree() {
    let text = agrees(INTS);
    assert!(text.starts_with("0 1 9223372036854775807 "), "{text}");
    same_trace(INTS);
}

#[test]
fn floats_agree() {
    let text = agrees(FLOATS);
    assert!(!text.is_empty());
    same_trace(FLOATS);
}

#[test]
fn texts_agree() {
    let text = agrees(TEXTS);
    assert!(text.starts_with("[|0|"), "{text}");
    same_trace(TEXTS);
}

#[test]
fn delays_agree() {
    assert_eq!(agrees(DELAYS), "20\n");
    same_trace(DELAYS);
}

/// Division as `%` and `/` compile to it, under every step limit and frame
/// limit up to the least that finishes: the same stopping points, no leak.
#[test]
fn division_stops_where_the_machine_does() {
    let source = r#"import Std (IO, List)

def digits: Nat → Nat → Nat → Nat
  | Zero, n, acc => acc
  | Succ fuel, n, acc => digits fuel (n / 10) (acc + n % 10)

def go: Nat → Nat
  | Zero => 0
  | Succ n => digits 40 1234567 0 + digits 40 (123456789012345678901234567890 + n) 0 + go n

def main(): {IO} () :=
  IO.print "${go 3}"
"#;
    with_stack(STACK, move || {
        let (program, limits) = lowered(source);
        every_limit_agrees(&program, limits);
    });
}
