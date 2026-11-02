-- expect-error: E-MATCH-MOTIVE
-- `match induct` proves propositions.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def countAbove (k: Nat): List Nat → Nat
  | Nil => 0
  | Cons x xs => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

def count (k: Nat) (xs: List Nat): Nat :=
  match induct (countAbove k xs) with
    | eq1 => 0
    | eq2IfTrue x xs h ih => 0
    | eq2IfFalse x xs h ih => 0
