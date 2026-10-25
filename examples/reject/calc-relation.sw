-- expect-error: E-CALC-RELATION
-- `<=` chains are on `Nat`; this chain is on lists.
theorem bad (xs: List Nat) (ys: List Nat) (h: xs = ys): xs = ys :=
  calc xs
    _ = ys := h
    _ ≤ ys
