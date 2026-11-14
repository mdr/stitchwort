-- A generalising `match` whose scrutinee holds `acc`'s type, an unknown
-- until `g 0` fixes it, waits for it (D2090). Meanwhile its own type, which
-- its alternatives fix, is compared with `Nat` by `g 0`: that comparison
-- waits for the `match` too, and holds once it is resumed.

import Std (List)

def plus (a b: Nat): Nat := a + b

def f (n: Nat): Nat :=
  let g := acc =>
    match List.length [acc] with
      | Zero => 0
      | Succ k => plus acc k
  g 0

test "the waiting match is resumed" := f 3 == 0
