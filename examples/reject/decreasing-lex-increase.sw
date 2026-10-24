-- expect-error: E-DECREASING
-- With `decreasing (m, n)`, a call may let the second measure grow only when
-- the first gets smaller. This one makes the first bigger, so the pair
-- doesn't come before the parameters': the message shows both pairs and
-- what would do.
import Std (Nat)

def grow (m: Nat) (n: Nat): Nat
    decreasing (m, n)
:=
  match n with
    | Zero => m
    | Succ j => grow (m + 1) j
