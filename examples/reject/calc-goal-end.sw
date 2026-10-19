-- expect-error: E-CALC-GOAL
-- The chain ends at `c`, but the goal's right side is `d`.
theorem bad (a: Nat) (b: Nat) (c: Nat) (d: Nat) (h1: a = b) (h2: b = c): a = d :=
  calc a
    _ = b := h1
    _ = c := h2
