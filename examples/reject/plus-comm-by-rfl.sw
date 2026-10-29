-- expect-error: E-REFL
-- `n + m = m + n` is true, but not by computation: `+` computes on a side
-- only when it is a number or a `Succ`, and both are unknown here. It needs
-- a proof by induction (`Nat.addComm`). `n + 0 = n` and `n + 1 = Succ n` are
-- by computation (accept/plus-both-sides.sw).
theorem plusComm (n: Nat) (m: Nat): n + m = m + n := rfl
