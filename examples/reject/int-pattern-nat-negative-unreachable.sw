-- expect-error: E-TYPE-MISMATCH
-- The `(-1)` equation can never run (the wildcard above it catches
-- everything), but it is still ill-typed on a `Nat` and so still rejected.
def f: Nat → Nat
  | 0 => 1
  | _ => 2
  | (-1) => 3
