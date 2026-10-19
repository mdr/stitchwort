-- expect-error: E-PARSE
-- A block must end with an expression, not a definition.
def f (n: Nat): Nat :=
  def g (k: Nat): Nat := k
