-- expect-error: E-AMBIGUOUS
-- Two names imported as `n`: an error only where `n` is used, listing both.
import Std.List (length as n, reverse as n)

def x: Nat := n [1, 2]
