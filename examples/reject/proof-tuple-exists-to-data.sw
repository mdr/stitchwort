-- expect-error: E-PROP-ELIM
-- A tuple on a proof of `∃` is `Witness` written shorter, so neither can
-- return the witness as data.
def viaTuple (h: ∃ (n: Nat) => n > 2): Nat :=
  let (n, _) := h
  n
