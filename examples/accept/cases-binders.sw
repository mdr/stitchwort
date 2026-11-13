-- `cases` introduces a goal's leading binders (docs/proposals/decide.md
-- §6.1.1) when nothing proves the `Π` goal as it stands. A statement's
-- variables go before the colon, as in these examples.
import Std (Bool, Nat, Void)

def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal

def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

-- Day 12's truth table, its variables before the colon.
theorem rowEndsAfter ∀ (plot out side sideOut: Bool):
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- All four before the colon.
theorem rowEndsMixed ∀ (plot: Bool) (out: Bool) (side sideOut: Bool):
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- A hypothesis the contradiction closer uses in the case `b = False`.
theorem hypAfter ∀ (b: Bool) (h: b = True): not b = False := cases

-- A named one.
theorem unnamedHyp ∀ (b: Bool) (h: b = False): (b ∧ True) = False := cases

-- A `Π` reached only after a split.
theorem piAfterSplit ∀ (b: Bool): if b then (∀ (x: Bool) => not (not x) = x) else (b = False) := cases

-- An implicit binder after an explicit one.
theorem implicitInside ∀ (a: Bool) [b: Bool]: (a ∧ b) = (b ∧ a) := cases
