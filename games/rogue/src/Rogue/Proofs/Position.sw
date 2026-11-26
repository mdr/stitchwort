--| Small facts about numbers and cells that the proofs share: `==` on them
--| and when two cells are the same.

namespace Rogue.Proofs
import Rogue (..)
import Std (DecEq, Eq, Nat, Void)

--| A cell is its row and column (the checker doesn't use this by itself).
theorem positionEta ∀ (p: Position): p = { row = p.row, column = p.column } := match p with
  | { row = r, column = c } => byComputing

theorem positionExt ∀ (p q: Position) (sameRow: p.row = q.row) (sameColumn: p.column = q.column): p = q :=
  Eq.trans (positionEta p) (rewrite sameRow, sameColumn then Eq.flipped (positionEta q))

--| Two cells on the same row that aren't the same cell are in different columns.
theorem columnDiffers ∀ (p q: Position)
    (differ: (p == q) = False)
    (sameRow: (p.row == q.row) = True):
    (p.column == q.column) = False :=
  let notSame := differ.read
  match sameColumn: p.column == q.column with
    | True => Void.impossible (notSame (positionExt p q sameRow.read sameColumn.read))
    | False => byComputing
