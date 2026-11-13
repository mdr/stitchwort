-- expect-warning: W-MATCH-NOT-FOUND
-- The warning's "computed" note is for a goal that shows the expression as
-- written (`isBig 20` in `pick (isBig 20) = 1`), decided on terms: `f x` is
-- not in `f xs`, so no note claims the goal contains it (SW-2554 review, F4).
import Std (Nat)

def double (n: Nat): Nat := n + n

theorem prefix ∀ (x: Nat) (xs: Nat): double xs = xs + xs := match h: double x with
  | Zero => rfl
  | Succ k => rfl
