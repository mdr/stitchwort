-- An update of a field several constructors share, written again in a
-- proof's body: like a `match`, it becomes a helper only once the body is
-- elaborated, and is compared with the program's then, by what it does.

import Std (Eq, Nat)

type Shape =
  | Dot (ref: Nat) (id: Nat)
  | Circle (ref: Nat) (id: Nat) (radius: Nat)

def setId (c: Shape) (x: Nat): Shape := { c | id = x }

theorem setIdCong (c: Shape) (x: Nat) (y: Nat) (h: x = y): setId c x = setId c y :=
  Eq.cong (v => { c | id = v }) h
