-- expect-error: E-MATCH-MOTIVE
-- A generalising `match` whose expected type is an unknown that only its
-- alternatives fix (`apply2`'s `c`). It can't wait for that, so its motive
-- is checked when its helper is lifted, once `c` is `Nat`: with every
-- variable it copied, `q`'s copy included, which the alternatives don't use
-- (D2090). Pairs with accept/match-motive-goal-later.sw.

import Std (List)

def one (m: Nat) (p: m = 1): Bool → Nat
  | True => m
  | False => 0

def apply2 (f: a → c) (v: a): c := f v

-- Generalising `length [n]` (which is 1) makes `q`'s type ill-formed.
def later (b: Bool) (q: one 1 rfl b = 1) (n: Nat): Nat :=
  apply2 (r => match List.length [n] with
    | Zero => 0
    | Succ k => k) n
