-- expect-error: E-UNKNOWN-FIELD
-- `x` depends on `y` in `C` and `y` depends on `x` in `D`: no order of the
-- two fields works for the generated function.

import Std (Vec)

type U =
  | C (x: Nat) (y: Vec Nat x)
  | D (y: Nat) (x: Vec Nat y)

def xOf (u: U): Nat := u.x
