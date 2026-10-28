-- A `Comp` whose results are a variable `r`, not its row's, is a data type
-- like any other: a value of it is passed as it is, and its operations'
-- row isn't read from it (SW-851; reject/comp-row-results-variable.sw has
-- the plain value that isn't one).
import Std.Effect (Comp, NoOp)

def pass (c: Comp NoOp r Nat): Comp NoOp r Nat := c
def passTwice (c: Comp NoOp r Nat): Comp NoOp r Nat := pass (pass c)
theorem passIsSame (c: Comp NoOp r Nat): passTwice c = c := rfl
