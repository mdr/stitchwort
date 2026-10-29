-- Does today's `cases` already prove day 12's truth table?
import Std (Bool)

def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal
def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

theorem rowEndsSplit (plot: Bool) (out: Bool) (side: Bool) (sideOut: Bool):
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases
