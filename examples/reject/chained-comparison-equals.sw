-- expect-error: E-COMPARISON-CHAIN
-- `=` and `==` don't chain (for now).
def bad (a b c: Nat): Bool := a == b == c
