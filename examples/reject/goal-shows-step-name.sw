-- expect-error: E-REFL
-- Rewriting with a `decreasing` definition's `unfold` leaves its `%step`
-- helper in the goal. It takes the recursive function as an argument, so it
-- isn't simply the definition's name or its body: showing that would mean
-- unfolding it with the argument in place (SW-4274).

import Std (Nat)

def half (n: Nat): Nat decreasing n :=
  if h: n < 2 then 0 else half (n - 2) + 1

theorem halfZero (n: Nat): half n = 0 :=
  rewrite half.unfold n
