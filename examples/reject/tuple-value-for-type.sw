-- expect-error: E-NOT-A-TYPE
-- A tuple of values isn't a type.
f : (1, 2) -> Nat
f _ = 0
