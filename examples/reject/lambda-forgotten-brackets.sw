-- expect-error: E-TYPE-MISMATCH
-- `map x => x + 1` was meant to pass a lambda to `map`: it is a lambda with
-- parameters `map` and `x`, so its type doesn't fit, and the error says how to
-- fix it.
import List (map)

def bump (xs: List Nat) : List Nat := map x => x + 1
