-- expect-error: E-REFL
-- `n + 0 = n` is true, but not by computation: `+` recurses on its first
-- argument, which is unknown here. It needs a proof by induction.
theorem plusZero (n : Nat) : n + 0 = n := rfl
