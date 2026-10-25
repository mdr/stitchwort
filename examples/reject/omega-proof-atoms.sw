-- expect-error: E-OMEGA
-- Two proofs of `n < 10` give two different atoms, even though the proposition is the same.
import Std (Nat)

def getP: (n: Nat) → n < 10 → Nat
  | Zero,   h => 0
  | Succ k, h => k

theorem twoProofs (n: Nat) (h1: n < 10) (h2: n < 10): getP n h1 ≤ getP n h2 := omega
