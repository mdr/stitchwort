-- expect-error: E-PARSE
-- A step is `=`, `<=` or `<`: `!=` can't be chained.
theorem bad (a: Nat) (b: Nat) (h: a != b): a != b :=
  calc a
    _ != b := h
