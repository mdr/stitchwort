-- expect-error: E-MATCH-MOTIVE
-- Pairs with reject/match-motive-hypothesis-annotated.sw: the same `match`,
-- with the hypothesis `q`'s type an ordinary unknown until the later
-- argument `x.pf` fixes it. The occurrence test can't find `1` in an
-- unknown, so the `match` waits for it, then copies `q` as the annotated
-- one does (D2090).

import Std (List)

def one (m: Nat) (p: m = 1): Bool → Nat
  | True => m
  | False => 0

type Box (b: Bool) = { pf: one 1 rfl b = 1 }

def apply [a: Prop] (f: a → Nat) (v: a): Nat := f v

-- Generalising `length [1]` (which is 1) makes `q`'s type ill-formed.
def later (b: Bool) (x: Box b): Nat :=
  apply (q => match List.length [1] with
    | Zero => 0
    | Succ k => k) x.pf
