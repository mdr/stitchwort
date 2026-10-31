-- D2086: a `match` on `1 + 1`. On main the literals are `Nat` at once, the
-- scrutinee computes to `2`, `q`'s type mentions `2`, so it is generalised
-- and the motive is ill-formed (E-MATCH-MOTIVE). With the literals waiting
-- (stage 4's experiment) the scrutinee is `?a + ?b`, which the occurrence
-- test finds nowhere, so nothing is generalised and the program is accepted.
def two (m: Nat) (p: m = 2): Bool → Nat
  | True => m
  | False => 0

def bad (b: Bool) (q: two 2 rfl b = 2): Nat := match 1 + 1 with
  | Zero => 0
  | Succ k => k
