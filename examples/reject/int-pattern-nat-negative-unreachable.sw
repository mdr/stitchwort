-- expect-error: E-TYPE-MISMATCH
-- The `(-1)` equation can never run (the wildcard above it catches
-- everything), but it is still ill-typed on a `Nat` and so still rejected.
f : Nat -> Nat
f 0 = 1
f _ = 2
f (-1) = 3
