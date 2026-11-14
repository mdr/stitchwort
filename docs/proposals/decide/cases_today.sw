-- Does today's `cases` already prove day 12's truth table?
import Std (Bool)

def convex (plot vertical horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal
def concave (plot vertical horizontal diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

theorem rowEndsSplit ∀ (plot out side sideOut: Bool):
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut))
      = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases
