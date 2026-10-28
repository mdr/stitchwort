-- expect-error: E-REFL
-- `all` over a literal list computes to the `&&` of its elements and the
-- `True` of its empty case. What the two sides compute to is long, and its
-- inner parts are shown as `…`, so the message names where they first
-- differ: `… && True` against `…`.

import Std (List)

def p (k: Nat) (x: Nat): Bool := x * k + (k + (x + 1)) == x * x + (k * x + (x + (k + 7)))

theorem allFour (c: Nat):
    (List.range 4 |> .all (p c)) = (p c 0 && p c 1 && p c 2 && p c 3) := rfl
