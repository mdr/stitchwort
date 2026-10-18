-- expect-error: E-LET-REFUTABLE
-- Rejected by design: coverage is by the type `Maybe Nat`, not by the value;
-- docs/proposals/syntax-conveniences.md section 5.1.
three : Nat
three =
  let Just x = Just 3
  x
