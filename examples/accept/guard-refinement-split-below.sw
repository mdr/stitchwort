-- Below a guard that refines a proof's goal, arms that split the list and
-- bind its fields still see them: the arms below are compiled before the
-- refinement binds its variables, and are moved past them (SW-4388).
import Std (List)

def firstPlus (skip: Bool) (xs: List Nat): Nat := match skip, xs with
  | s, _ if s => 0
  | _, [] => 1
  | _, [x, .._] => x + 1

theorem succPositive ∀ (x: Nat): 0 < x + 1 := arithmetic

theorem firstPlusZeroOrPositive ∀ (skip: Bool) (xs: List Nat): firstPlus skip xs = 0 ∨ 0 < firstPlus skip xs :=
  match skip, xs with
    | s, _ if s => Inl byComputing
    | _, [] => Inr byComputing
    | _, [x, .._] => Inr (succPositive x)
