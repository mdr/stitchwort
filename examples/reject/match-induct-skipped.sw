-- expect-error: E-NO-INDUCT
-- A recursive definition whose `f.induct` can't be made gets none; the error says why.
import Std (Bool, Eq, List, Nat, Option, Or, Void)

def pick (d: Nat): List Nat → Nat
  | Nil => d
  | Cons x rest =>
    match x with
      | 0 => d
      | _ => pick d rest

theorem pickLe (d: Nat) (xs: List Nat): pick d xs ≥ 0 :=
  match induct (pick d xs) with
    | eq1 d => omega
