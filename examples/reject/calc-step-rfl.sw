-- expect-error: E-CALC-STEP
-- `byComputing` as a step's proof is checked against the step's equation.
theorem bad (n: Nat) (m: Nat): n + m = m + n :=
  calc n + m
    _ = m + n := byComputing
