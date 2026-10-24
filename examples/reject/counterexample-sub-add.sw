-- expect-error: E-REFL
-- Truncated subtraction: `(a - b) + b = a` is false at `a = 0, b = 1`. With
-- the missing hypothesis added the statement is true, so the second
-- theorem's (still wrong) proof gets no note (acceptance test 2).
theorem subAdd (a: Nat) (b: Nat): (a - b) + b = a := rfl

theorem subAddBelow (a: Nat) (b: Nat) (h: b <= a): (a - b) + b = a := rfl
