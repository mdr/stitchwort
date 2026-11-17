-- `False` in a statement is the `Bool` `False`, read as the proposition
-- `False = True` (SW-2901). A goal of `False = True` has no proof unless
-- the hypotheses contradict each other; for a proposition with no proof,
-- write `Void`.
theorem noProof ∀ (n: Nat): n = 0 → False := n0 => ?
