-- expect-error: E-PARSE
-- Haskell's `[2..n]`: the spread is `[2, ..n]`, and a range needs no brackets.
import Std (List, Nat)

def numbers (n: Nat): List Nat := [2..n]
