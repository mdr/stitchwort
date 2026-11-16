-- expect-error: E-REWRITE-REPEATEDLY-RULE

import Std (Nat)

def f (x: Nat): Nat := x + x

-- `h`'s `y` is on its right side only: finding `f a` says nothing about
-- it, so the rule would put an unknown into the goal. It is refused where
-- it is listed; `h _ 3` gives it.
theorem bad ∀ (a: Nat) (h: ∀ (x y: Nat) => f x = y + x): f a = 3 + a := rewrite repeatedly [h]
