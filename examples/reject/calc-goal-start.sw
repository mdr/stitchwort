-- expect-error: E-CALC-GOAL
-- The chain starts at `b`, but the goal's left side is `a`.
theorem bad (a: Nat) (b: Nat) (c: Nat) (h1: b = c): a = c :=
  calc b
    _ = c := h1
