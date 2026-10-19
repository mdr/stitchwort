-- expect-error: E-CALC-STEP
-- The proof of the second step proves `b <= c`, but the line says `b < c`.
theorem bad (a: Nat) (b: Nat) (c: Nat) (h1: a <= b) (h2: b <= c): a < c :=
  calc a
    _ <= b := h1
    _ < c := h2
