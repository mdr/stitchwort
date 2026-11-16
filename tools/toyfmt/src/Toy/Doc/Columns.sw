--| Two measures of the output, and one Bool fact: the width of the last
--| line (its pieces the last first), the width of an indent, and that a
--| conjunction's left side holds when the conjunction does. Words and
--| places use them; the `Tracks` and `Measured` invariants that used to
--| live here were never reached from the final theorems.

namespace Toy.Doc.Proofs
import Toy.Doc (..)
import Std (Bool, Eq, List, Nat, Text)

--| The characters on the last line of the output (its pieces the last
--| first).
def lineWidth: List Text → Nat
  | [] => 0
  | [piece, ..earlier] => if piece == "\n" then 0 else piece.length + lineWidth earlier

theorem indentLength ∀ (indent: Nat): (" ".repeat indent).length = indent := match indent with
  | Zero => byComputing
  | Succ less => Eq.cong Succ (indentLength less)

theorem andTrueLeft ∀ (left right: Bool) (both: (left && right) = True): left = True := match left, both with
  | True, _ => byComputing
