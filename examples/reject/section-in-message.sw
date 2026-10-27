-- expect-error: E-REFL
-- An operator section in a message is shown as written: `(== id)` and
-- `(id ==)`, not as the lambda it elaborates to.
theorem countFlipped (xs: List Nat) (id: Nat): xs.count (== id) = xs.count (id ==) := rfl
