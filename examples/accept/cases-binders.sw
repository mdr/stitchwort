-- `cases` introduces a goal's leading binders (docs/proposals/decide.md
-- §6.1.1) when nothing proves the `Π` goal as it stands: a statement's
-- variables may be bound after the colon as well as before it.
import Std (Bool, Nat, Void)

def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal

def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

-- Day 12's truth table with its variables after the colon: the same proof
-- as `plot out side sideOut => cases` (examples/accept/cases-pi-goals.sw).
theorem rowEndsAfter: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- Two before the colon, two after.
theorem rowEndsMixed (plot: Bool) (out: Bool): (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- A hypothesis after the colon, which the contradiction closer uses in the
-- case `b = False`.
theorem hypAfter: (b: Bool) → b = True → not b = False := cases

-- An unnamed one.
theorem unnamedHyp: (b: Bool) → (b = False) → (b ∧ True) = False := cases

-- A `Π` reached only after a split.
theorem piAfterSplit (b: Bool): if b then ((x: Bool) → not (not x) = x) else (b = False) := cases

-- An implicit binder after an explicit one.
theorem implicitInside: (a: Bool) → [b: Bool] → (a ∧ b) = (b ∧ a) := cases
