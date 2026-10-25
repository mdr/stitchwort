-- expect-error: E-PARSE
-- An operator section takes one operand, the one that binds tighter than its
-- operator: `(+ 1 + 2)` could mean `x + 1 + 2` or `x + (1 + 2)`, so it's an
-- error. Bracket the operand: `(+ (1 + 2))`.

def f (xs: List Nat): List Nat := xs.map (+ 1 + 2)
