-- expect-error: E-UNKNOWN-NAME
-- `halves` fails (the bracket goes to the `2` that `* 2` multiplies by, not
-- to the recursive call), so it has no `.unfold`; the proofs that use it
-- report no second error about that.

import Std (Nat)

def halves (m: Nat) (n: Nat): Nat
    decreasing m + n
:=
  if some: Nat.leq (m + n) 0 = False
  then 1 + halves (m / 2) (n / 2) * 2 [decreasing := Nat.leRefl 0]
  else 0

theorem halvesNone: halves 0 0 = 0 :=
  rewrite halves.unfold 0 0 in rfl

def halvesOfSeven: Nat := halves 3 4
