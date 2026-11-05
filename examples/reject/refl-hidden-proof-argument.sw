-- expect-error: E-REFL
-- Both sides print as `transported n m` but use different proofs of
-- `n = m`, which `transported` computes with (`J`); `rfl` can't make them
-- equal, and the message shows the proofs in brackets (SW-28). Proofs a
-- definition never computes with are skipped (accept/proof-irrelevance.sw).

import Std (Nat)

def transported (n: Nat) (m: Nat): [auto ok: n = m] → Nat := J (y e => Nat) n ok

theorem differentProofs (n: Nat) (m: Nat) (h1: n = m) (h2: n = m):
    transported n m [ok := h1] = transported n m [ok := h2] := rfl
