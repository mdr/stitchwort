-- expect-error: E-CALC-STEP
-- Equal ends don't make `n < n` hold: the step's proposition, not the
-- ends, is checked by computation.
theorem bad (n: Nat): n < n :=
  calc n
    _ < n
