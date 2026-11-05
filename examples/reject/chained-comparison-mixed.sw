-- expect-error: E-COMPARISON-CHAIN
-- A chain goes one way: `>` can't follow `<=`.
def bad (a b c: Nat): Bool := a <= b > c
