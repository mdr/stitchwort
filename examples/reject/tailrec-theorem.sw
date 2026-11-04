-- expect-error: E-ATTRIBUTE
-- Only definitions can be loops.
import Std (Nat)

@[tailrec]
theorem one: 1 = 1 := rfl
