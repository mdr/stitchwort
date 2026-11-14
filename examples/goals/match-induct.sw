-- A hole in each alternative of `match induct` shows the case's variables and the generalised
-- hypothesis `found` refined (docs/proposals/function-equations.md §5.3).
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def firstBig: List Nat → Option Nat
  | [] => None
  | [x, ..rest] =>
    match big: Nat.leq 10 x with
      | True => Some x
      | False => firstBig rest

theorem firstBigIsBig ∀ (xs: List Nat) (y: Nat) (found: firstBig xs = Some y): Nat.leq 10 y = True :=
  match induct (firstBig xs) with
    | eq1 => ?
    | eq2True x rest big => ?
    | eq2False x rest big ih => ?
