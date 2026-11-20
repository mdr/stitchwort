-- A user's binder named `x` is a written name, not one the compiler made:
-- the leaf's `arithmetic` reads the facts from it. The compiler marks its own
-- binders with `%`, so `x` is not skipped.

import Std (Parse, Nat)

def same (n: Nat): {Parse Nat} Nat := n

theorem givesSameBound ∀ (a b c: Nat) (x: a ≤ b ∧ b ≤ c): Parse.Gives Parse.Invariant.any (() => same a) (n => n ≤ c) :=
  byWalking []
