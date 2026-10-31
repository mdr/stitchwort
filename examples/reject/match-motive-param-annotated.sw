-- expect-error: E-MATCH-MOTIVE
-- Pairs with reject/match-motive-param-later.sw, with `r` annotated.

import Std (List)

type P = { x: Nat }

def one (m: Nat) (p: m = 1): Bool → Nat
  | True => m
  | False => 0

def apply (f: a → Nat) (v: a): Nat := f v

-- Generalising `length [r]` (which is 1) makes `q`'s type ill-formed.
def annotated (b: Bool) (q: one 1 rfl b = 1) (p: P): Nat :=
  apply ((r: P) => match List.length [r] with
    | Zero => 0
    | Succ k => k) p
