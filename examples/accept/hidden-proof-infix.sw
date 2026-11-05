-- `x % 7` fills in a proof that `7 != 0`. `Int.mod` never computes with it,
-- so two calls with different proofs are equal, through the notation as
-- written out (docs/core.md, "Proof irrelevance").

import Std (Int)

theorem differentProofs (x: Int) (h1: OfNat 7 ≠ OfNat 0) (h2: OfNat 7 ≠ OfNat 0):
    Int.mod x 7 [ok := h1] = Int.mod x 7 [ok := h2] := rfl

theorem notation (x: Int) (h: OfNat 7 ≠ OfNat 0): x % 7 = Int.mod x 7 [ok := h] := rfl
