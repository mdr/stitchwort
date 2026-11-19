-- `match induct (f args) with` on a std function: its `f.induct` is made
-- when the file needs it, without naming `f.induct` anywhere (SW-4260).
import Std (Bool, Eq, List, Nat)

theorem dropWhileLength ∀ (p: Nat → Bool) (xs: List Nat): List.length (List.dropWhile xs p) ≤ List.length xs :=
  match induct (List.dropWhile xs p) with
    | eq1 _ => arithmetic
    | eq2IfTrue p x xs h ih => arithmetic
    | eq2IfFalse p x xs h => arithmetic
