-- expect-error: E-EFFECT-ORDER
-- A computation in a call runs once, at the call (§4.5 R4), so it can't
-- wait for a parameter the call leaves out: `readVec()`'s type needs the
-- missing `n` (D1113).

import Std (Vec)

def readVec [n: Nat] (): {IO} (Vec Nat n) :=
  IO.print "reading"
  Vec.replicate n 0

def use (n: Nat) (xs: Vec Nat n): Nat := n

def main(): {IO} () :=
  let used := use (xs := readVec())
  IO.print "done"
