-- expect-error: E-CALC-GOAL
-- The chain proves `a < c`, which isn't the goal `a <= c`.
theorem bad (a: Nat) (b: Nat) (c: Nat) (h1: a ≤ b) (h2: b < c): a ≤ c :=
  calc a
    _ ≤ b := h1
    _ < c := h2
