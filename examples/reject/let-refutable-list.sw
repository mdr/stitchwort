-- expect-error: E-LET-REFUTABLE
-- `Cons x _` doesn't cover `Nil`, so the `let` can fail.
def first (xs: List Nat): Nat :=
  let Cons x _ := xs
  x
