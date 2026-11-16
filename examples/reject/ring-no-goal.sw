-- expect-error: E-ALGEBRA
-- With no expected type, `algebra` asks for one: `(algebra: a = b)`.
import Std (Nat)

def noGoal (x: Nat): Nat :=
  let p := algebra
  x
