-- expect-error: E-REFL
-- No K-like rule: `J` on a proof variable doesn't compute, even at `n = n`.
-- Partner: `jOnRfl` in accept/proof-irrelevance.sw.
import Std (Nat)

theorem t5 (n: Nat) (h: n = n) (d: Nat): J (y e => Nat) d h = d := rfl
