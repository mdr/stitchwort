-- expect-error: E-TYPE-MISMATCH
-- As mismatch-hidden-proof-argument.sw, through the `%` notation: `x % 7`
-- prints without its proof that `7 != 0`, so the two types print the same.
-- The message shows the calls with their proofs in brackets (SW-323).

import Std (Int)

theorem differentProofs (x: Int) (h1: OfNat 7 != OfNat 0) (h2: OfNat 7 != OfNat 0)
    (p: Int.mod x 7 [ok := h2] = Int.mod x 7 [ok := h2]):
    Int.mod x 7 [ok := h1] = Int.mod x 7 [ok := h1] := p
