--| Slice 1's formatter on small cases: what `formatWithin` prints, and what
--| it refuses. The harness (`dev/fmt-twin s1`) compares every declaration
--| within the slice with the Rust formatter's; these pin the rules' main
--| shapes, each expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

def formats (source expected: Text): Bool := formatWithin source == Ok expected

def refuses (source: Text): Bool := match formatWithin source with
  | Err message => message.startsWith "outside slice"
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

test "a closer after a trailing comment goes left of the lines inside its brackets" :=
  formats "def d: ( -- t7\n    a -- t9\n  ) -- t10\n  := b\n" "def d: ( -- t7\n    a -- t9\n) -- t10\n  :=\n  b\n"

test "a token outside the alphabet, or a construct outside the slice, is refused" :=
  refuses "def x: Nat := r.field\n" && refuses "def f (n: Nat := 1): Nat := n\n" && refuses "def x: Nat := (a: Nat)\n"
