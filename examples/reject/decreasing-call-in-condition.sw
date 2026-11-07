-- expect-error: E-DECREASING
-- A recursive call in an `if`'s condition isn't supported yet, even where
-- an `if` around it would give the call its fact (SW-2145, F1).
import Std (Nat)

def climbBoth (n: Nat) (i: Nat): Nat
    decreasing n - i
:=
  if (if i + 2 ≤ n then climbBoth n (i + 2) else 0) + i < n
  then climbBoth n (i + 1)
  else 0
