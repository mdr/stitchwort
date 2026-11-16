-- expect-error: E-TYPE-MISMATCH
-- Too few parts is not an error by itself: the last part stands for the
-- rest of the chain, and the note says what it had to prove.
theorem small: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byComputing)
