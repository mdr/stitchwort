-- expect-error: E-REFL
-- Updates of different fields are different values, however alike they look
-- (SW-386, D1091).

import Std (Nat)

type Shape =
  | Dot (ref: Nat) (id: Nat)
  | Circle (ref: Nat) (id: Nat) (radius: Nat)

def setRef (c: Shape) (x: Nat): Shape := { c | ref = x }
def setId (c: Shape) (x: Nat): Shape := { c | id = x }

theorem different (c: Shape) (x: Nat): setRef c x = setId c x := rfl
