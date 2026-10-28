-- expect-error: E-TYPE-MISMATCH
-- The neighbour of comp-row-results-variable.sw where the `Comp` is the
-- result of a function argument. `apply`'s `r` is unknown while the lambda
-- is checked, so the lambda's plain body is a computation in the empty row
-- and solves `r` with that row's `NoRes`; `apply`'s result then isn't
-- `two`'s, whose `r` is a variable. The elaborator reports it, not the
-- kernel (SW-851).
import Std.Effect (Comp, NoOp)

def apply (k: Nat → Comp NoOp r Nat): Comp NoOp r Nat := k 1
def two: Comp NoOp r Nat := apply (n => n + 1)
