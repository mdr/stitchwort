-- expect-error: E-TYPE-MISMATCH
-- Two types that print the same until the arguments the compiler fills in are
-- shown: `Int.modNat x (Succ t)` takes a proof that `Succ t != 0`, and these
-- two use different proofs of it, which aren't interchangeable (SW-28). The
-- message shows them in brackets.

theorem differentProofs (x: Int) (t: Nat) (h1: Succ t != 0) (h2: Succ t != 0)
    (p: Int.modNat x (Succ t) [ok := h2] = Int.modNat x (Succ t) [ok := h2]):
    Int.modNat x (Succ t) [ok := h1] = Int.modNat x (Succ t) [ok := h1] := p
