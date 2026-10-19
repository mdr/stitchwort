-- expect-error: E-CALC-STEP
-- A step with no proof must hold by computation. `n + 1` is stuck on `n`
-- (`+` recurses on its first argument), so it isn't `Succ n`.
theorem bad (n: Nat): n + 1 = Succ n :=
  calc n + 1
    _ = Succ n
