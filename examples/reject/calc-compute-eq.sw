-- expect-error: E-CALC-STEP
-- A step with no proof must hold by computation. `n + m` is stuck on both
-- `n` and `m` (`+` computes on either side only when that side is a number
-- or a `Succ`), so it isn't `m + n`: that is a theorem, `Nat.addComm`.
theorem bad (n: Nat) (m: Nat): n + m = m + n :=
  calc n + m
    _ = m + n
