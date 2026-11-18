--| Slice 4b's formatter on small cases: list, tuple, bracketed and absurd
--| patterns, named arguments and annotations. The harness (`dev/fmt-twin
--| s4b`) compares every declaration within slices 1 to 5a and 4b with the
--| Rust formatter's; these pin the main shapes, each expected text being
--| `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "list patterns, a tail, tuples and `(p)`" :=
  formats
      "def len: List Nat → Nat\n  | [] => 0\n  | [x, ..xs] => 1 + len xs\ndef sum (pair: (Nat, Nat)): Nat := match pair with\n  | (a, b) => a + b\ndef f: Option (List Nat) → Nat\n  | Some [x] => x\n  | Some [x, y, ..rest] => x + y\n  | Some (Cons x _) => x\n  | None => 0\ndef p: Option Nat → Nat\n  | (Some x) => x\n  | (None) => 0\n"
      "def len: List Nat → Nat\n  | [] => 0\n  | [x, ..xs] => 1 + len xs\ndef sum (pair: (Nat, Nat)): Nat := match pair with | (a, b) => a + b\ndef f: Option (List Nat) → Nat\n  | Some [x] => x\n  | Some [x, y, ..rest] => x + y\n  | Some (Cons x _) => x\n  | None => 0\ndef p: Option Nat → Nat\n  | (Some x) => x\n  | (None) => 0\n"

test "an absurd arm, and tuple patterns after `let`" :=
  formats
      "def g (n: Empty): Nat := match n with\n  | ()\ndef h: Nat := let (a, b) := (1, 2); a\ndef k (x: Nat): Nat :=\n  let (a, _) := (x, x)\n  a\n"
      "def g (n: Empty): Nat := match n with | ()\ndef h: Nat := let (a, b) := (1, 2); a\ndef k (x: Nat): Nat :=\n  let (a, _) := (x, x)\n  a\n"

test "a long list pattern breaks one item a line, a long tuple of names fills, a comment breaks a list" :=
  formats
      "def long: List (Nat, Nat, Nat) → Nat\n  | [(aaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccccccccccc), (dddddddddddddddddd, eeeeeeeeeeeeeeeeeeeee, ffffff), ..rest] => 0\n  | _ => 1\ndef t: (Nat, Nat, Nat, Nat) → Nat\n  | (aaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccccccccccccc, ddddddddddddddddddddddddddddd) => 0\ndef c: List Nat → Nat\n  | [ -- head\n    x, ..xs] => x\n  | [] => 0\n"
      "def long: List (Nat, Nat, Nat) → Nat\n  | [\n      (aaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccccccccccc),\n      (dddddddddddddddddd, eeeeeeeeeeeeeeeeeeeee, ffffff),\n      ..rest\n    ] => 0\n  | _ => 1\ndef t: (Nat, Nat, Nat, Nat) → Nat\n  | (aaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccccccccccccc,\n      ddddddddddddddddddddddddddddd) => 0\ndef c: List Nat → Nat\n  | [ -- head\n      x,\n      ..xs\n    ] => x\n  | [] => 0\n"

test "a constructor with a list argument keeps its plain arguments on the line" :=
  formats
      "def q: Pair (Option Nat) (List Nat) → Nat\n  | Pair aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb [cccccccccccccccccccccccc, ddddddddddddddddddddd] => 0\n  | Pair _ _ _ => 1\n"
      "def q: Pair (Option Nat) (List Nat) → Nat\n  | Pair aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n      [cccccccccccccccccccccccc, ddddddddddddddddddddd] => 0\n  | Pair _ _ _ => 1\n"

test "named arguments and type annotations" :=
  formats
      "def a: Nat := f (n := 1) (m := g x) y\ndef b: Nat := (x: Nat) + (f y : List Nat).length\ndef c: Nat := someFunctionWithALongName (argument := aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) (other := bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb + 1)\ndef d: Nat :=\n  f (n := -- why\n    1)\ndef e: Nat := (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb ccccccccccccccccccccccccccc : Nat)\n"
      "def a: Nat := f (n := 1) (m := g x) y\ndef b: Nat := (x: Nat) + (f y: List Nat).length\ndef c: Nat :=\n  someFunctionWithALongName\n    (argument := aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)\n    (other := bbbbbbbbbbbbbbbbbbbbbbbbbbbbbb + 1)\ndef d: Nat := f (n := -- why\n  1)\ndef e: Nat :=\n  (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n      ccccccccccccccccccccccccccc: Nat)\n"

test "a negative pattern, `.._` and the unit are outside the slice" :=
  refuses "def f: Int → Nat\n  | -1 => 0\n  | _ => 1\n"
    && refuses "def f: List Nat → Nat\n  | [x, .._] => x\n  | _ => 0\n"
    && refuses "def u: Unit := ()\n"
