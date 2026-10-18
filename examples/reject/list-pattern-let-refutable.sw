-- expect-error: E-LET-REFUTABLE
-- `[a, b]` doesn't cover other lengths, so the `let` can fail.
f : List Nat -> Nat
f xs =
  let [a, b] = xs
  a + b
