-- expect-error: E-CALC-STEP
-- `rfl` as a step's proof is checked against the step's equation.
theorem bad (n: Nat): n + 1 = 1 + n :=
  calc n + 1
    _ = 1 + n := rfl
