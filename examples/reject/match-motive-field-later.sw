-- expect-error: E-MATCH-MOTIVE
-- Pairs with reject/match-motive-field-annotated.sw: the same `match`, with
-- `r`'s type fixed only by the later argument `p`. The scrutinee holds
-- `r.x`, which waits for `r`'s type; the `match` waits for it too, then
-- generalises `q` as the annotated one does (D2090).

import Std (List)

type P = { x: Nat }

def two (m: Nat) (p: m = 2): Bool → Nat
  | True => m
  | False => 0

def apply (f: a → Nat) (v: a): Nat := f v

-- Generalising `length [r.x, r.x]` (which is 2) makes `q`'s type ill-formed.
def later (b: Bool) (q: two 2 rfl b = 2) (p: P): Nat :=
  apply (r => match List.length [r.x, r.x] with
    | Zero => 0
    | Succ k => k) p
