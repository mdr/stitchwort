-- Small facts about numbers and cells that the proofs share: `==` on them
-- and when two cells are the same.

namespace Rogue.Proofs
import Rogue (..)
import Std (DecEq, Eq, Nat, Void)

theorem natEqSelf (n: Nat): (n == n) = True := rewrite Nat.eqIsEqual n n, Nat.equalRefl n in rfl

theorem natSound (m: Nat) (n: Nat) (same: (m == n) = True): m = n := Nat.equalSound m n (rewrite <- Nat.eqIsEqual m n in same)

theorem zeroPlus (n: Nat): 0 + n = n := omega

-- A cell is its row and column (the checker doesn't use this by itself).
theorem positionEta: (p: Position) → p = { row = p.row, column = p.column }
  | { row = r, column = c } => rfl

theorem positionExt (p: Position) (q: Position) (sameRow: p.row = q.row) (sameColumn: p.column = q.column): p = q :=
  Eq.trans (positionEta p) (rewrite sameRow, sameColumn in Eq.sym (positionEta q))

-- Two cells on the same row that aren't the same cell are in different columns.
theorem columnDiffers (p: Position) (q: Position) (differ: (p == q) = False) (sameRow: (p.row == q.row) = True): (p.column == q.column) = False :=
  match sameColumn: p.column == q.column with
    | True => Void.exfalso (DecEq.soundFalse p q differ (positionExt p q (natSound p.row q.row sameRow) (natSound p.column q.column sameColumn)))
    | False => rfl
