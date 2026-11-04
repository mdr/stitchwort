-- expect-error: E-REFL
-- Effectful functions are data, never proofs (an effectful function's
-- result can't be a proposition). Partner: `unitBoxes` in
-- accept/proof-irrelevance.sw.
import Std (Nat)

theorem t6 (f: Nat → {IO} Nat) (g: Nat → {IO} Nat): f = g := rfl
