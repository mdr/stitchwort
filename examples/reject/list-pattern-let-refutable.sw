-- expect-error: E-LET-REFUTABLE
-- `[a, b]` doesn't cover other lengths, so the `let` can fail.
def f (xs: List Nat): Nat :=
  let [a, b] := xs
  a + b
