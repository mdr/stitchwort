-- expect-error: E-RING
-- With no expected type, `ring` asks for one: `(ring: a = b)`.
import Std (Nat)

def noGoal (x: Nat): Nat :=
  let p := ring
  x
