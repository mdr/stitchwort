-- expect-error: E-INDUCT-CASE
-- Two alternatives for one case.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def countAbove (k: Nat): List Nat → Nat
  | Nil => 0
  | Cons x xs => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem le (k: Nat) (xs: List Nat): countAbove k xs ≤ List.length xs :=
  match induct (countAbove k xs) with
    | eq1 => omega
    | eq2IfTrue x xs h ih => omega
    | eq2IfTrue x xs h ih => omega
    | eq2IfFalse x xs h ih => omega
