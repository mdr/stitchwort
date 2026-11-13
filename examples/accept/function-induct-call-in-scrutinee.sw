-- `settle.induct`, for a `decreasing` definition that calls itself in a
-- `match`'s scrutinee as well as in an alternative: the scrutinee's call
-- is in the cases' hypotheses (`settle rest = None`), as the equations
-- state it, and only the alternative's call gets an induction hypothesis.
import Std (Eq, List, Nat, Option)

def settle (xs: List Nat): Option Nat
    decreasing xs.length
:= match xs with
  | [] => None
  | [_, ..rest] =>
    if shorter: rest.length < xs.length then
      match settle rest with
        | None => None
        | Some _ => settle rest
    else None

theorem settleNone ∀ (xs: List Nat): settle xs = None :=
  settle.induct
    (xs result => result = None)
    rfl
    (x rest shorter none => rfl)
    (x rest shorter n some ih => ih)
    (x rest notShorter => rfl)
    xs
