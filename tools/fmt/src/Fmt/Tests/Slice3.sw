--| Slice 3's formatter on small cases: blocks, `let`, `if` and `match`.
--| The harness (`dev/fmt-twin s3`) compares every declaration within slices
--| 1 to 3 with the Rust formatter's; these pin the rules' main shapes, each
--| expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "a block keeps its lines, its blank lines and comments, and a `let` its type" :=
  formats "def a: Nat :=\n  let x := 1\n  let y:Nat := x+2\n\n\n  -- comment\n  f x y\n"
      "def a: Nat :=\n  let x := 1\n  let y: Nat := x + 2\n\n  -- comment\n  f x y\n"

test "an `if` is one line if it fits, else a clause a line; an `else if` chain never one line" :=
  formats
      "def b: Nat := if c then d else e\ndef c: Nat := if someLongConditionName aaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbb then someValueHereThatIsLong cccccccccc else dddddddddddddddddddddd eeeeeeeeeee\ndef d: Nat := if a then b else if c then d else e\n"
      "def b: Nat := if c then d else e\ndef c: Nat :=\n  if someLongConditionName aaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbb then someValueHereThatIsLong cccccccccc\n  else dddddddddddddddddddddd eeeeeeeeeee\ndef d: Nat :=\n  if a then b\n  else if c then d\n  else e\n"

test "a `match` hugs the `:=` line, one arm sharing its line, a nested `match` below its arm" :=
  formats
      "def e: Nat := match x with | Zero => 1\ndef h: Nat := match a, b with\n  | Cons x _, n if n > 0 => match y with\n    | z => z\n  | _, _ => 0\n"
      "def e: Nat := match x with | Zero => 1\ndef h: Nat := match a, b with\n  | Cons x _, n if n > 0 =>\n    match y with\n      | z => z\n  | _, _ => 0\n"

test "an expression `let` lines up after its `;`, a lambda before the `;` keeps its body" :=
  formats "def e: Nat := (let x := 1; -- semi\n  x + 1)\ndef f: Nat := (let g := y => y; g 1)\n"
      "def e: Nat :=\n  (let x := 1; -- semi\n   x + 1)\ndef f: Nat := (let g := y => y; g 1)\n"

test "a block in brackets opens below them, and a block branch below its keyword" :=
  formats "def i: Nat := f (\n  let x := 1\n  x)\ndef j: Nat :=\n  if a then\n    let x := 1\n    x\n  else\n    2\n"
      "def i: Nat := f (\n  let x := 1\n  x)\ndef j: Nat :=\n  if a then\n    let x := 1\n    x\n  else 2\n"

test "a comment after the last parameter puts a `match` body below the header" :=
  formats "def a (x: Nat) -- about x\n    : Nat := match x with\n  | Zero => 1 -- one\n  -- the rest\n  | Succ n => n\n"
      "def a (x: Nat) -- about x\n    : Nat :=\n  match x with\n    | Zero => 1 -- one\n    -- the rest\n    | Succ n => n\n"

test "a later block line starting with `-` is outside the slice" :=
  refuses "def i (x y: Int): Int :=\n  let z := x + y\n  - z\n"

test "an own-line comment between an expression `let`'s `:=` and its value keeps the value at the block's column and the body after the `;`" :=
  formats "def bracketed: Nat :=\n  (let x :=\n  -- c\n  1; x)\n\ndef plain: Nat :=\n  let x :=\n  -- c\n  1; x\n"
      "def bracketed: Nat :=\n  (let x :=\n  -- c\n  1; x)\n\ndef plain: Nat :=\n  let x :=\n  -- c\n  1; x\n"
