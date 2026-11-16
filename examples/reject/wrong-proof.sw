-- expect-error: E-REFL
-- A false statement can't be proved by `byComputing`.
theorem wrong: 2 + 2 = 5 := byComputing
