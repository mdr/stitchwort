-- expect-error: E-TYPE-MISMATCH
-- Two types that print the same until the arguments the compiler fills in are
-- shown: `transported n m` takes a proof that `n = m` and computes with it
-- (`J`), so calls with two different proofs of it differ (SW-28). The
-- message shows the proofs in brackets. A proof a definition never computes
-- with, like `Fin.ofNatLt`'s, is skipped instead (accept/proof-irrelevance.sw).

import Std (Nat)

def transported (n: Nat) (m: Nat): [auto ok: n = m] → Nat := J (y e => Nat) n ok

theorem differentProofs (n: Nat) (m: Nat) (h1: n = m) (h2: n = m)
    (p: transported n m [ok := h2] = transported n m [ok := h2]):
    transported n m [ok := h1] = transported n m [ok := h1] := p
