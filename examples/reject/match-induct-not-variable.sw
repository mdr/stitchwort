-- expect-error: E-MATCH-MOTIVE
-- The arguments in the motive places must be variables; the fixed prefix may be any terms.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def countAbove (k: Nat): List Nat → Nat
  | Nil => 0
  | Cons x xs => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

theorem le (k: Nat) (xs: List Nat): countAbove k (Cons 1 xs) ≤ List.length xs + 1 :=
  match induct (countAbove k (Cons 1 xs)) with
    | eq1 => omega
    | eq2IfTrue x xs h ih => omega
    | eq2IfFalse x xs h ih => omega
