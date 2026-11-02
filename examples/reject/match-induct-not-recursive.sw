-- expect-error: E-NO-INDUCT
-- A function that does not call itself has no `f.induct`.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def countAbove (k: Nat): List Nat → Nat
  | Nil => 0
  | Cons x xs => if Nat.leq k x then Succ (countAbove k xs) else countAbove k xs

def double (n: Nat): Nat := n + n

theorem big (n: Nat): double n ≥ n :=
  match induct (double n) with
    | eq1 n => omega
