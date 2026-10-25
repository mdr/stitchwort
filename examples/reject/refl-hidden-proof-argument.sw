-- expect-error: E-REFL
-- Both sides print as `Int.modNat x (Succ t)` but use different proofs of
-- `Succ t != 0`; `rfl` can't make them equal, and the message shows the proofs
-- in brackets (SW-28).

import Std (Int)

theorem differentProofs (x: Int) (t: Nat) (h1: Succ t ≠ 0) (h2: Succ t ≠ 0):
    Int.modNat x (Succ t) [ok := h1] = Int.modNat x (Succ t) [ok := h2] := rfl
