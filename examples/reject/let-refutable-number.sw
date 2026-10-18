-- expect-error: E-LET-REFUTABLE
-- A number pattern only matches that number.
zero : Nat -> Nat
zero n =
  let 0 = n
  1
