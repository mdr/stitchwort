-- SW-206 (4), (5): `a <= b` where a `Bool` is expected is `Nat.leq a b` itself,
-- so a proof about one is a proof about the other, and `match h: a <= b with`
-- works like `match h: Nat.leq a b with`.
import Std (Nat, Int, Bool)

def below (a b: Nat): Bool := a ≤ b
def strictlyBelow (a b: Nat): Bool := a < b
def belowInt (a b: Int): Bool := a ≤ b
def strictlyBelowInt (a b: Int): Bool := a < b

-- They are the comparison, by `rfl`: no `Decidable.holds (Bool.decTrue …)` in between.
theorem belowIsLeq ∀ (a b: Nat): below a b = Nat.leq a b := rfl
theorem strictlyBelowIsLeq ∀ (a b: Nat): strictlyBelow a b = Nat.leq (Succ a) b := rfl
theorem belowIntIsLeq ∀ (a b: Int): belowInt a b = Int.leq a b := rfl
theorem strictlyBelowIntIsLess ∀ (a b: Int): strictlyBelowInt a b = Int.less a b := rfl

-- A `Bool` fact about `<=` inside `&&` is what `Nat.leq` says, with no lemma in between.
theorem andLeftLeq ∀ (a b c: Nat) (h: (a ≤ b ∧ b ≤ c) = True): Nat.leq a b = True := Bool.andLeft h

def inside (lo x hi: Nat): Bool := lo ≤ x ∧ x ≤ hi

-- Matching on either spelling gives the same branches.
theorem outsideAbove ∀ (lo x hi: Nat) (h: hi < x): inside lo x hi = False := match e: lo ≤ x with
  | True => Nat.leqFalseOfLess hi x h
  | False => rfl

theorem outsideAboveLeq ∀ (lo x hi: Nat) (h: hi < x): inside lo x hi = False := match e: Nat.leq lo x with
  | True => Nat.leqFalseOfLess hi x h
  | False => rfl
