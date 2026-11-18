--| Two measures of the output, and one Bool fact: the width of the last
--| line (its pieces the last first), the width of an indent, and that a
--| conjunction's left side holds when the conjunction does. Words and
--| places use them; the `Tracks` and `Measured` invariants that used to
--| live here were never reached from the final theorems.

import Doc (..)
import Doc.Proofs (..)

--| The characters on the last line of the output (its pieces the last
--| first).
def Doc.Proofs.lineWidth: List Text → Nat
  | [] => 0
  | [piece, ..earlier] => if piece == "\n" then 0 else piece.length + lineWidth earlier

--| `indent` spaces are `indent` characters long.
theorem Doc.Proofs.indentLength ∀ (indent: Nat): (" ".repeat indent).length = indent := match indent with
  | Zero => byComputing
  | Succ less => Eq.cong Succ (indentLength less)

--| The left side of a true conjunction is true.
theorem Doc.Proofs.andTrueLeft ∀ (left right: Bool) (both: (left && right) = True): left = True := match left, both with
  | True, _ => byComputing
