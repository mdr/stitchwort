-- expect-error: E-REFL
-- What a side computes to is shown with the number on the right, as sums
-- are written: the right side computes to `x + 2`, not `2 + x` (SW-895).
theorem notEqual (x: Nat): x + 3 = Succ (x + 1) := rfl
