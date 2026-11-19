-- expect-error: E-OR-PATTERN-BINDS
-- The cases of one arm bind the same names: `h` would have no value in `eq1`.
import Std (Bool, Eq, List, Nat)

def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem countAboveLe ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs := match induct (countAbove k xs) with
  | eq1 | eq2IfTrue _ _ h _ | eq2IfFalse _ _ _ _ => arithmetic
