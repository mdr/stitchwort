-- expect-error: E-LET-REFUTABLE
-- A refutable pattern nested inside a tuple is still refutable.
def firstOf (p: (Maybe Nat, Nat)): Nat :=
  let (Just a, b) := p
  a + b
