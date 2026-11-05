-- expect-error: E-COMPARISON-CHAIN
-- `in` doesn't chain.
def bad (a b: Nat) (xs: List Nat): Bool := a <= b in xs
