-- expect-error: E-PARSE
-- The relation goes on its own line, after `_`.
theorem bad (a: Nat) (b: Nat) (h: a = b): a = b :=
  calc a = b := h
