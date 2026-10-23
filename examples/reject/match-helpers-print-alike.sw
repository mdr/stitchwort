-- expect-error: E-REFL
-- Two different `match`es written in different definitions are two different
-- hidden functions that print alike: the message says so (SW-319, D552).
-- Identical ones are now equal (SW-386, D1091), so these differ in `None`.

import Std (List, Option)

def foo (xs: List (Option Nat)): Nat := xs.foldLeft (acc o => match o with | Some x => acc + x | None => acc) 0
def bar (xs: List (Option Nat)): Nat := xs.foldLeft (acc o => match o with | Some x => acc + x | None => acc + 1) 0

theorem same (xs: List (Option Nat)): foo xs = bar xs := rfl
