-- expect-error: E-COMPARISON-CHAIN
-- `!=` doesn't chain: `a != b != c` would not mean that all three differ.
def bad (a b c: Nat): Bool := a != b != c
