--| Slice 4a's formatter on small cases: field access and dot calls. The
--| harness (`dev/fmt-twin s4a`) compares every declaration within slices
--| 1 to 4a with the Rust formatter's; these pin the main shapes, each
--| expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "a field access is glued, in chains, dot calls and types" :=
  formats
      "def a: Nat := x.f.g + (f x).length\ndef b: Nat := xs.foldLeft (acc x => acc + x.value) 0\ntheorem t (xs: List Nat): xs.length = xs.reverse.length := xs.lengthReverse\n"
      "def a: Nat := x.f.g + (f x).length\ndef b: Nat := xs.foldLeft (acc x => acc + x.value) 0\ntheorem t ∀ (xs: List Nat): xs.length = xs.reverse.length := xs.lengthReverse\n"

test "a field of a name stays on a broken call's line" :=
  formats
      "def c: Nat := someFunctionName a.b c.d (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb) (ccccccccccccccccccccccccccc dddd)\n"
      "def c: Nat :=\n  someFunctionName a.b c.d\n    (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb)\n    (ccccccccccccccccccccccccccc dddd)\n"

test "a method section, a field after a commented bracket and `- 1.f` are outside the slice" :=
  refuses "def a: Nat := f .g\n" && refuses "def b: Nat := (x -- c\n  ).g\n" && refuses "def c: Int := - 1.abs\n"
