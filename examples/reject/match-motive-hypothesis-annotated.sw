-- expect-error: E-MATCH-MOTIVE
-- Pairs with reject/match-motive-hypothesis-later.sw, with `q` annotated.

import Std (List)

def one (m: Nat) (p: m = 1): Bool → Nat
  | True => m
  | False => 0

type Box (b: Bool) = { pf: one 1 rfl b = 1 }

def apply [a: Prop] (f: a → Nat) (v: a): Nat := f v

-- Generalising `length [1]` (which is 1) makes `q`'s type ill-formed.
def annotated (b: Bool) (x: Box b): Nat :=
  apply ((q: one 1 rfl b = 1) => match List.length [1] with
    | Zero => 0
    | Succ k => k) x.pf
