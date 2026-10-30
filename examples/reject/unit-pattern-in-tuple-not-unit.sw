-- expect-error: E-NOT-EMPTY
-- `()` inside a tuple pattern is the unit pattern only where what it
-- matches is `()` (accept/unit-pattern-in-tuple.sw, SW-886). Here it
-- matches a `Nat`, which has values, so it can't be the absurd pattern
-- either; `_` ignores it.
def first (p: (Nat, Nat)): Nat :=
  let (n, ()) := p
  n
