import Std (Nat, Vec)

def clampTo (limit n: Nat): Nat := if n ≤ limit then n else limit

theorem clampToAtMost ∀ (limit n: Nat): clampTo limit n ≤ limit := match fits: Nat.leq n limit with
  | True => ?
  | False => ?
