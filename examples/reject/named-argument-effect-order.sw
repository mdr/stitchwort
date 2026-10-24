-- expect-error: E-EFFECT-ORDER
-- A computation runs once, where it's written (§4.5 R1, R4): `readVec()`'s
-- type needs `n`, which a computation written after it gives, so the call
-- is refused rather than run out of order (D1113).

import Std (Vec)

def readVec [n: Nat] (): {IO} (Vec Nat n) :=
  IO.print "reading"
  Vec.replicate n 0

def readNat(): {IO} Nat :=
  IO.print "counting"
  3

def use (n: Nat) (xs: Vec Nat n): Nat := n

def main(): {IO} () :=
  let used := use (xs := readVec()) (n := readNat())
  IO.print "${used}"
