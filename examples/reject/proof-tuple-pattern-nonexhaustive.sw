-- expect-error: E-NONEXHAUSTIVE
-- The case a proof's tuple pattern leaves out is written as a tuple, the
-- way a pattern for it would be.
theorem opened ∀ (h: ∃ (n: Nat) => n = 7 ∧ n > 1): 1 = 1 := match h with | (0, a, b) => byComputing
