-- expect-error: E-REFL
-- `rfl` is the equation itself, never a proof of a reading: against
-- `(b == b) = True` it means `b == b` is `True`, which doesn't compute for a
-- variable `b`. `DecEq.refl b` proves it.
import Std (Bool, Nat)

theorem same (b: Nat): (b == b) = True := rfl
