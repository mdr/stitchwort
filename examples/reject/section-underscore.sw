-- expect-error: E-CANNOT-INFER
-- `_.isZero` is a hole followed by a field access, not a function: `_` is for
-- the compiler to fill in. To pass the method as a function, write the method
-- section `.isZero` (docs/syntax.md, "Method sections").

def f (xs: List Nat): Nat := xs |> .count _.isZero
