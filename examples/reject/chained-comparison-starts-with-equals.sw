-- expect-error: E-COMPARISON-CHAIN
-- A chain can't start with `=` either: `a = b < c` is not `a = b && b < c`.
def bad (a b c: Nat): Bool := a = b < c
