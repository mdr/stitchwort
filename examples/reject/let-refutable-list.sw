-- expect-error: E-LET-REFUTABLE
-- `Cons x _` doesn't cover `Nil`, so the `let` can fail.
first : List Nat -> Nat
first xs =
  let Cons x _ = xs
  x
