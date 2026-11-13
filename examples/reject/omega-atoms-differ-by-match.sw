-- expect-error: E-OMEGA
-- The `match` replaced `x <= y` by `True` in the goal; the fact stated inside
-- it still says `x <= y`, so the two atoms differ and `omega` says why.

import Std (Nat, Bool)

theorem refined ∀ (g: Bool → Nat) (k: Nat) (bound: ∀ (b: Bool) => g b ≤ k) (x y: Nat): g (x <= y) ≤ k :=
  match x <= y with
    | True => omega [bound (x <= y)]
    | False => omega [bound (x <= y)]
