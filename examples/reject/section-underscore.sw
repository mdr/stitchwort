-- expect-error: E-CANNOT-INFER
-- `_.isZero` is a hole followed by a field access, not a function: `_` is for
-- the compiler to fill in, and it has no type to look `.isZero` up in. There
-- is no placeholder syntax for a function's argument (D1194, D1196); see
-- docs/syntax.md, "Method sections".

def f (xs: List Nat): Nat := xs |> .count _.isZero
