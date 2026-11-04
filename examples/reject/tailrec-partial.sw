-- expect-error: E-ATTRIBUTE
-- A partial definition is run by its own machine; not covered yet.
import Std (Nat)

@[tailrec]
def countdown (n: Nat): {Partial} Nat := if n == 0 then 0 else countdown (n - 1)
