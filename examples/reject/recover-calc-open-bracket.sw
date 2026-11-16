-- expect-error: E-PARSE
-- A bracket left open in a `calc` step runs out at the next step: inside a
-- `calc`, a line starting with `_` is always the next step. That is one
-- syntax error, at the `_`, and the steps after it are still read.
theorem stepUp (m n: Nat) (h: n ≤ m): 0 ≤ m :=
  calc 0
    _ ≤ n(
    _ ≤ m := h
