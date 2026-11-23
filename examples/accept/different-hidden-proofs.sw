-- Calls of a function variable `t` with two different proofs of `n = m`
-- in its hidden argument are the same call: by rule I any two proofs are
-- equal, unlooked-at (docs/core.md, "Proof irrelevance"), whatever `t`
-- might do with its proof. So the types below match, and `byComputing`
-- proves the equation. Before rule I both were refused (SW-28), with the
-- proofs shown in brackets; calls differing in a data argument the
-- compiler fills in still are (reject/mismatch-hidden-implicit-argument.sw,
-- reject/refl-hidden-implicit-argument.sw).

import Std (Nat)

theorem differentProofs ∀ (n m: Nat) (t: [auto ok: n = m] → Nat)
    (h1 h2: n = m)
    (p: t [ok := h2] = t [ok := h2]):
    t [ok := h1] = t [ok := h1] :=
  p

theorem differentProofsComputed ∀ (n m: Nat) (t: [auto ok: n = m] → Nat) (h1 h2: n = m): t [ok := h1] = t [ok := h2] :=
  byComputing
