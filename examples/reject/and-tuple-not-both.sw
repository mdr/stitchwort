-- expect-error: E-CANNOT-INFER
-- A pair is not a proof of a conjunction: `a ∧ b` is built with `Both`,
-- its constructor, as in `Both rfl h`.
theorem t ∀ (a: Nat) (h: a = 1): a = a ∧ a = 1 := (rfl, h)
