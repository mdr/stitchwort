-- Two proofs of `n < 10` give one atom: `getP` never computes with its
-- proof, so `getP n h1` and `getP n h2` are the same term to `omega`, as to
-- `rfl` (docs/core.md, "Proof irrelevance").
import Std (Nat)

def getP: (n: Nat) → n < 10 → Nat
  | Zero, h => 0
  | Succ k, h => k

theorem twoProofs ∀ (n: Nat) (h1: n < 10) (h2: n < 10): getP n h1 ≤ getP n h2 := omega
