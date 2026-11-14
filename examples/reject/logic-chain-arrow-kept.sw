-- expect-error: E-TYPE-MISMATCH
-- The `→ q` after a chain of three is part of the statement, so `h`, a
-- proof of `a ∧ a ∧ a`, doesn't prove it.
theorem kept ∀ (a q: Prop) (h: a ∧ a ∧ a): a ∧ a ∧ a → q := h
