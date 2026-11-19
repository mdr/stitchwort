-- `match induct (f args) with ?` lists every case of `f.induct`: its name,
-- the names its alternative binds, and its goal, to start from.
import Std (Bool, Eq, List, Nat)

def countAbove (k: Nat): List Nat → Nat
  | [] => 0
  | [x, ..xs] => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem le ∀ (k: Nat) (xs: List Nat): countAbove k xs ≤ xs.length := match induct (countAbove k xs) with ?
