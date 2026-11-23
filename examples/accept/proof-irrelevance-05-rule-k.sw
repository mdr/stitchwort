-- Rule K (docs/core.md, "The equality rule"): `J` into data on a proof
-- variable computes when the ends of its equation are equal, here `n` and
-- `n`; the proof is never looked at. Was soundness/proof-irrelevance-05-no-k.sw,
-- refused (E-REFL) while `J` computed on `byComputing` only. Partner:
-- `jOnRfl` in accept/proof-irrelevance.sw.
import Std (Nat)

theorem t5 ∀ (n: Nat) (h: n = n) (d: Nat): J (y e => Nat) d h = d := byComputing
