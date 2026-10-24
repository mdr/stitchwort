-- expect-error: E-EFFECT-ORDER
-- A positional call runs its computations first too, in written order
-- (docs/proposals/named-arguments.md §4.5): `readVec()`'s length `n` is an
-- unknown made when it runs, and `same` ties it to `k`, which `say 2` gives
-- later, so it can't be found from it. Running `say 2` first with a `let`
-- works.

import Std (Vec)

def readVec [n: Nat] (): {IO} (Vec Nat n) :=
  IO.print "readVec"
  Vec.replicate n 0

def say (n: Nat): {IO} Nat :=
  IO.print "arg ${n}"
  n

def sized [n: Nat] (xs: Vec Nat n) (k: Nat) (same: n = k): Nat := k

def main(): {IO} () :=
  let r := sized (readVec()) (say 2) rfl
  IO.print "${r}"
