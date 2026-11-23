-- expect-error: E-TYPE-MISMATCH
-- Two types that print the same until the arguments the compiler fills in are
-- shown: `t` is a function variable taking a proof that `n = m`, and calls
-- of it with two different proofs differ (SW-28). The message shows the
-- proofs in brackets. A proof a definition never computes with, like
-- `Fin.ofNatLt`'s, is skipped instead (accept/proof-irrelevance.sw), and so
-- is one a definition only casts along (rule K: casts along two proofs of one
-- equation are compared by their ends, never by the proofs).

import Std (Nat)

theorem differentProofs ∀ (n m: Nat) (t: [auto ok: n = m] → Nat)
    (h1 h2: n = m)
    (p: t [ok := h2] = t [ok := h2]):
    t [ok := h1] = t [ok := h1] :=
  p
