-- expect-error: E-REFL
-- Both sides print as `t` but use different proofs of `n = m`, and `t` is a
-- function variable, which might compute with its proof; `byComputing` can't
-- make them equal, and the message shows the proofs in brackets (SW-28).
-- Proofs a definition never computes with are skipped
-- (accept/proof-irrelevance.sw), as are proofs it only casts along (rule K).

import Std (Nat)

theorem differentProofs ∀ (n m: Nat) (t: [auto ok: n = m] → Nat) (h1 h2: n = m): t [ok := h1] = t [ok := h2] :=
  byComputing
