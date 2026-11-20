--| Slice 1's formatter on small cases: what `formatWithin` prints, and what
--| it refuses. The harness (`dev/fmt-twin s1`) compares every declaration
--| within the slice with the Rust formatter's; these pin the rules' main
--| shapes, each expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Fmt.Later (formatWithin)
import Std (Bool, Result, Text)

def formats (source expected: Text): Bool := formatWithin source == Ok expected

def refuses (source: Text): Bool := match formatWithin source with
  | Err message => message.startsWith "outside slice"
  | Ok _ => False

--| Whether the source is refused for any reason: outside the slices, or a parse error the Rust parser gives too.
def fails (source: Text): Bool := match formatWithin source with
  | Err _ => True
  | Ok _ => False

test "a slice 1 file is tidied and spaced" :=
  formats "def x:Nat:=f  (a,b)  [1,2,] -  -y\n" "def x: Nat := f (a, b) [1, 2] - -y\n"

test "a prefix minus before a numeral's application keeps its space" :=
  formats "def y: Int := - 2 n\n" "def y: Int := - 2 n\n"

test "blank lines and comments between declarations are kept, one blank line at most" :=
  formats "-- a\ndef x: Nat := 1\n\n\n-- b\n\ndef y: Nat := 2 -- c\n-- end\n"
      "-- a\ndef x: Nat := 1\n\n-- b\n\ndef y: Nat := 2 -- c\n-- end\n"

test "a long call goes below the `:=`, its last arguments at 4" :=
  formats
      "def long: Nat := someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive (another call here)\n"
      "def long: Nat :=\n  someFunction argumentNumberOne argumentNumberTwo argumentNumberThree argumentNumberFour argumentNumberFive\n    (another call here)\n"

test "a call hugs its last argument, a list, when the list can't fit below" :=
  formats
      "def hug: List Nat := f [aaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccccccc, dddddddddddddddddddddd, eeeeeeeeeeeeeeeee + 1]\n"
      "def hug: List Nat := f [\n  aaaaaaaaaaaaaaaaaaaaa,\n  bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n  cccccccccccccccccccccccccccc,\n  dddddddddddddddddddddd,\n  eeeeeeeeeeeeeeeee + 1\n]\n"

test "a hugged last argument after a comment has its items under its bracket and its closer at the bracket's column" :=
  formats
      "def x: List Nat := f\n  -- the pairs\n  (firstLongArgumentName, secondLongArgumentName, thirdLongArgumentName, fourthLongArgumentName)\n"
      "def x: List Nat := f\n  -- the pairs\n  (\n    firstLongArgumentName,\n    secondLongArgumentName,\n    thirdLongArgumentName,\n    fourthLongArgumentName\n  )\n"

test "a closer after a trailing comment goes left of the lines inside its brackets" :=
  formats "def d: ( -- t7\n    a -- t9\n  ) -- t10\n  := b\n" "def d: ( -- t7\n    a -- t9\n) -- t10\n  :=\n  b\n"

test "a closer with a comment, after a last item with one, follows it with no empty line" :=
  formats "def x: T := [\n  aaa, -- c\n  bbb -- e\n] -- d\ndef y: T := {\n  a = aaa, -- c\n  b = bbb -- e\n} -- d\n"
      "def x: T := [\n  aaa, -- c\n  bbb -- e\n] -- d\ndef y: T := {\n  a = aaa, -- c\n  b = bbb -- e\n} -- d\n"

test "a blank line before a filled list's first cell is dropped, not left to break its groups" :=
  formats "def d: A := g [\n\n  f, a]\n" "def d: A := g [f, a]\n"

test "a last comma's trailing comment keeps the comma's blank line above it" :=
  formats "def d: A := f [g -- t12\n  -- o13\n\n , -- t14\n]\n" "def d: A := f [g -- t12\n  -- o13\n\n  -- t14\n]\n"

test "a last comma on a line of its own leaves a blank line between the comments around it" :=
  formats "def d: A := f [g\n  -- o2\n  ,\n  -- o3\n]\n" "def d: A := f [g\n  -- o2\n\n  -- o3\n]\n"

test "comments above the type's or the value's first token put it on a line of its own" :=
  formats "def d:\n  -- c\n  F A := b\n" "def d:\n    -- c\n    F A :=\n  b\n"
    && formats "def g: A :=\n  -- c\n  f b\n" "def g: A :=\n  -- c\n  f b\n"

test "a walk followed by more of an expression is refused, as the Rust parser refuses it" :=
  fails "def a: T := byWalking [x] y\n" && fails "def a: T := byWalking [x] + 1\n"

test "`byWalking` is a keyword: as an operand or a name it is refused, as the Rust parser refuses it" :=
  fails "def a: T := x + byWalking [y]\n" && fails "def byWalking: Nat := 1\n" && fails "def a: byWalking := b\n"

test "a plain walk is slice 6a's, formatted as the Rust formatter does" :=
  formats "def a: T := byWalking  [x,y]\n" "def a: T := byWalking [x, y]\n"

test "a token outside the alphabet, or a construct outside the slice, is refused" :=
  refuses "def x: Nat := f .field\n" && refuses "def f (n: Nat := 1): Nat := n\n" && refuses "def x: Unit := ()\n"

test "a comma that starts the closer's line, with a comment above it, leaves the comments where Rust does" :=
  -- Without the comma the closer at the item's column wouldn't parse; the
  -- Rust P2 deletes the comma from the text and settles again.
  formats "def x: T := g ([\n    1\n    -- above\n  , ] -- b\n  ) -- c\n"
      "def x: T :=\n  g\n    ([1\n      -- above\n    ] -- b\n    ) -- c\n"

test "a closer's comment stays on it when a last comma with no comment starts the closer's line" :=
  formats "def x: T := g ([\n    1 -- a\n  , ] -- b\n  )\n" "def x: T :=\n  g\n    ([\n      1 -- a\n    ]) -- b\n"

def settles (source: Text): Bool := match formatWithin source with
  | Ok once => formatWithin once == Ok once
  | Err _ => False

test "a comment line ending in two carriage returns keeps none and formats the same twice" :=
  settles "-- a\r\r\ndef d: A := b\n"
    && settles "def d: A := b\n-- a\r\r\n"
    && settles "def d: A := b -- a\r\r\n"
    && formats "-- a\r\r\ndef d: A := b\n" "-- a\ndef d: A := b\n"

test "a carriage return inside a comment, not at its end, is kept" := settles "def d: A := b -- a\rb\r\n"

test "a comment ending in carriage returns and spaces, in any order, loses all of them and formats the same twice" :=
  settles "-- a\r \ndef d: A := b\n"
    && settles "-- a \r\ndef d: A := b\n"
    && settles "-- a\r \r\ndef d: A := b\n"
    && settles "def d: A := b\n-- a\r \r \n"
    && settles "def d: A := b -- a \r \r\n"
    && formats "-- a\r \ndef d: A := b\n" "-- a\ndef d: A := b\n"
    && formats "-- a\r \r\ndef d: A := b\n" "-- a\ndef d: A := b\n"

test "a carriage return or tab that text follows in a comment is kept and the output is stable" :=
  settles "-- a\r\t\ndef d: A := b\n" && settles "-- a\rb\ndef d: A := b\n" && settles "def d: A := b -- a\rb \r\n"

-- A blank line above an own-line comment is kept wherever the source has one (D3693); the expected texts are
-- `stitchwort fmt`'s (crates/fmt golden `comment-blank-above`).

test "a blank line above a comment over a call's argument is kept" :=
  formats "def argument: A := f\n\n  -- c\n  x\n" "def argument: A :=\n  f\n\n    -- c\n    x\n"

test "a blank line above a comment over an operator's right operand is kept" :=
  formats "def operand: Nat := a +\n\n  -- c\n  b\n" "def operand: Nat :=\n  a\n    +\n\n      -- c\n      b\n"

test "a blank line above a comment over an operator is kept" :=
  formats "def operandBefore: Nat := a\n\n  -- c\n  + b\n" "def operandBefore: Nat :=\n  a\n\n    -- c\n    + b\n"

test "a blank line above a comment over a list's closer is kept" :=
  formats "def closer: List Nat := [\n  1,\n  2\n\n  -- c\n]\n" "def closer: List Nat := [1, 2\n\n  -- c\n]\n"

test "a blank line above a comment over a bracket's closer is kept" :=
  formats "def parenCloser: Nat := (a\n\n  -- c\n)\n" "def parenCloser: Nat :=\n  (a\n\n    -- c\n  )\n"

test "a blank line above a comment over the type is kept" :=
  formats "def resultType:\n\n  -- c\n  Nat := 1\n" "def resultType:\n\n    -- c\n    Nat :=\n  1\n"

test "a blank line above a comment over the value is kept" :=
  formats "def value: Nat :=\n\n  -- c\n  1\n" "def value: Nat :=\n\n  -- c\n  1\n"

test "a blank line above a comment over a list item is kept" :=
  formats "def item: List Nat := [\n  f a,\n\n  -- c\n  g b\n]\n"
      "def item: List Nat := [\n  f a,\n\n  -- c\n  g b\n]\n"

test "blank lines above and between comments are kept" :=
  formats "def twoComments: A := f\n\n  -- c\n\n  -- d\n  x\n"
      "def twoComments: A :=\n  f\n\n    -- c\n\n    -- d\n    x\n"
