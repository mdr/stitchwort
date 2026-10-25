-- expect-error: E-TYPE-MISMATCH
-- A computation over the empty row is run where a value is expected
-- (accept/empty-row-run.sw), but its type isn't the value's: a function
-- returning `Comp NoOp NoRes Nat` isn't a `Nat -> Nat` (SW-124).
import Std.Effect (Comp, NoOp, NoRes)

def next (n: Nat): Comp NoOp NoRes Nat := n + 1
def apply (k: Nat → Nat) (n: Nat): Nat := k n
def bad: Nat := apply next 1
