-- expect-error: E-TYPE-MISMATCH
-- A tuple pattern with more parts than the proof has: the last ones meet a
-- part that is neither a pair nor a proof of `∃` or `∧`.
theorem opened ∀ (h: ∃ (n: Nat) => n = 7): 1 = 1 :=
  let (n, a, b) := h
  rfl
