-- expect-error: E-LET-REFUTABLE
-- A refutable pattern nested inside a tuple is still refutable.
def firstOf (p: (Option Nat, Nat)): Nat :=
  let (Some a, b) := p
  a + b
