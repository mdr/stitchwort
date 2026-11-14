-- A generalising `match` whose expected type is an unknown that only its
-- alternatives fix (`apply2`'s `c`): its motive is checked when its helper
-- is lifted, and holds. `q`'s copy has the type `s = 1` (D2090). Pairs with
-- reject/match-motive-goal-later.sw.

import Std (List)

def apply2 (f: a → c) (v: a): c := f v

def fine (q: List.length [1] = 1) (n: Nat): Nat :=
  apply2
    (r =>
      match List.length [n] with
        | Zero => 0
        | Succ k => k)
    n

test "the motive checked when lifted" := fine rfl 5 == 0
