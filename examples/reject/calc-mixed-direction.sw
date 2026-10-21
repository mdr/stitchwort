-- expect-error: E-CALC-RELATION
-- A chain goes one way: `>` can't follow `<=`.
theorem bad (a: Nat) (b: Nat) (c: Nat) (h1: a <= b) (h2: c < b): c < b :=
  calc a
    _ <= b := h1
    _ > c := h2
