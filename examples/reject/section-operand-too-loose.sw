-- expect-error: E-PARSE
-- The operand of a section with its right operand missing must bind tighter
-- than the operator: `(a + b *)` could mean `(a + b) * x` or `a + (b * x)`.
-- Bracket the operand: `((a + b) *)`.

def f (a: Nat) (b: Nat) (xs: List Nat): List Nat := xs.map (a + b *)
