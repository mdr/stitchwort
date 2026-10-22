-- SW-206 (4), (5): `a <= b` where a `Bool` is expected is `Nat.leq a b` itself,
-- so a proof about one is a proof about the other, and `match h: a <= b with`
-- works like `match h: Nat.leq a b with`.
import Std (Nat, Int, Bool)

def below (a: Nat) (b: Nat): Bool := a <= b
def strictlyBelow (a: Nat) (b: Nat): Bool := a < b
def belowInt (a: Int) (b: Int): Bool := a <= b
def strictlyBelowInt (a: Int) (b: Int): Bool := a < b

-- They are the comparison, by `rfl`: no `Decidable.toBool (Bool.decTrue …)` in between.
theorem belowIsLeq (a: Nat) (b: Nat): below a b = Nat.leq a b := rfl
theorem strictlyBelowIsLeq (a: Nat) (b: Nat): strictlyBelow a b = Nat.leq (Succ a) b := rfl
theorem belowIntIsLeq (a: Int) (b: Int): belowInt a b = Int.leq a b := rfl
theorem strictlyBelowIntIsLess (a: Int) (b: Int): strictlyBelowInt a b = Int.less a b := rfl

-- A `Bool` fact about `<=` inside `&&` is what `Nat.leq` says, with no lemma in between.
theorem andLeftLeq (a: Nat) (b: Nat) (c: Nat) (h: (a <= b && b <= c) = True): Nat.leq a b = True :=
  Bool.andLeft (a <= b) (b <= c) h

def inside (lo: Nat) (x: Nat) (hi: Nat): Bool := lo <= x && x <= hi

-- Matching on either spelling gives the same branches.
theorem outsideAbove (lo: Nat) (x: Nat) (hi: Nat) (h: hi < x): inside lo x hi = False :=
  match e: lo <= x with
    | True  => Nat.leqFalseOfLess hi x h
    | False => rfl

theorem outsideAboveLeq (lo: Nat) (x: Nat) (hi: Nat) (h: hi < x): inside lo x hi = False :=
  match e: Nat.leq lo x with
    | True  => Nat.leqFalseOfLess hi x h
    | False => rfl
