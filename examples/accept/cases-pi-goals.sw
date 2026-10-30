-- `Π` goals `cases` proves as they stand, without introducing anything
-- (docs/proposals/decide.md §6.1.1, decide/binders.sw and closer_order.sw).
-- Binder introduction and the decision closer come after the closers that
-- prove these, so their terms, and hashes, are the ones `cases` gave before
-- either existed.
import Std (Bool, Nat, Void)

-- A hypothesis of exactly the goal's type.
theorem byHyp (f: Bool → Bool → Bool) (same: (a: Bool) → (b: Bool) → f a b = f b a): (a: Bool) → (b: Bool) → f a b = f b a := cases

-- `omega` refutes the hypothesis of a goal `P → Void`.
theorem notLess (n: Nat): n + 1 < n → Void := cases

-- The term after `in`, tried against the whole goal.
theorem byTerm: (a: Bool) → (b: Bool) → (a ∨ b) = (b ∨ a) := cases in Bool.orComm

-- A leading implicit binder, introduced by the checker before `cases` runs.
theorem implicitAfter: [b: Bool] → not (not b) = b := cases

-- A goal that decides `No`, in a case whose hypotheses contradict each
-- other: `omega` refutes `h`.
theorem falseGoalImpossibleCase (n: Nat) (h: n + 1 < n): 2 ∈ [1, 3] := cases

def convex (plot: Bool) (vertical: Bool) (horizontal: Bool): Bool := plot ∧ ¬vertical ∧ ¬horizontal

def concave (plot: Bool) (vertical: Bool) (horizontal: Bool) (diagonal: Bool): Bool := plot ∧ vertical ∧ horizontal ∧ ¬diagonal

-- Day 12's truth table, its variables before the colon.
theorem rowEndsBefore (plot: Bool) (out: Bool) (side: Bool) (sideOut: Bool):
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  cases

-- After the colon, introduced by hand.
theorem rowEndsLambda: (plot: Bool) → (out: Bool) → (side: Bool) → (sideOut: Bool) →
    Bool.toNat ((plot ∧ ¬out) ∧ ¬(side ∧ ¬sideOut)) = Bool.toNat (convex plot out side) + Bool.toNat (concave side sideOut plot out) :=
  plot out side sideOut => cases
