-- expect-error: E-TYPE-MISMATCH
-- The cases of one arm share its body, which is checked for each: `ih` is the
-- goal in the false branch but not in the true one, and the error names the
-- case it is in.
import Std (Bool, Eq, List, Nat)

def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 => arithmetic
  | eq2IfTrue x xs h ih | eq2IfFalse x xs h ih => ih
