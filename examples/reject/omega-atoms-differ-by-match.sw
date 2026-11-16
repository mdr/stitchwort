-- expect-error: E-ARITHMETIC
-- The `match` replaced `x <= y` by `True` in the goal; the fact stated inside
-- it still says `x <= y`, so the two atoms differ and `arithmetic` says why.

import Std (Nat, Bool)

theorem refined ∀ (g: Bool → Nat) (k: Nat) (bound: ∀ (b: Bool) => g b ≤ k) (x y: Nat): g (x <= y) ≤ k :=
  match x <= y with
    | True => arithmetic [bound (x <= y)]
    | False => arithmetic [bound (x <= y)]
