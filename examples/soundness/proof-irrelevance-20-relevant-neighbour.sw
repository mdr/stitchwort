-- expect-error: E-REFL
-- Skipping the inert `ok` doesn't skip the relevant `x`. Partner:
-- `sameMod` and its variants in accept/proof-irrelevance.sw.
import Std (Int, Nat)

theorem t20 (x: Int) (y: Int) (p: 100 ≠ 0):
    Int.modNat x 100 [ok := p] = Int.modNat y 100 [ok := p] := rfl
