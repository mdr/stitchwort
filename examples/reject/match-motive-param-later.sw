-- expect-error: E-MATCH-MOTIVE
-- Pairs with reject/match-motive-param-annotated.sw: the same `match`, with
-- the lambda parameter `r`'s type an ordinary unknown until the later
-- argument `p` fixes it. The scrutinee holds that unknown; the `match`
-- waits for it, then generalises `q` as the annotated one does (D2090).

import Std (List)

type P = { x: Nat }

def one (m: Nat) (p: m = 1): Bool → Nat
  | True => m
  | False => 0

def apply (f: a → Nat) (v: a): Nat := f v

-- Generalising `length [r]` (which is 1) makes `q`'s type ill-formed.
def later (b: Bool) (q: one 1 rfl b = 1) (p: P): Nat :=
  apply (r => match List.length [r] with
    | Zero => 0
    | Succ k => k) p
