-- expect-error: E-REFL
-- Skipping the inert `ok` doesn't skip the relevant `x`. Partner:
-- `sameMod` and its variants in accept/proof-irrelevance.sw.
import Std (Int, Nat)

def wrap (x: Int) (d: Nat) [auto ok: d ≠ 0]: Nat := Int.modNat x d

theorem t20 (x: Int) (y: Int) (p: 100 ≠ 0):
    wrap x 100 [ok := p] = wrap y 100 [ok := p] := rfl
