-- expect-error: E-PARSE
-- The facts of `omega` are terms, not a list value.
theorem t (xs: List Nat) (h: 1 < 2): 0 < 2 := omega [h, ..xs]
