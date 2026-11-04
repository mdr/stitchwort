-- expect-error: E-ATTRIBUTE
import Std (Nat)

def f (n: Nat): Nat :=
  @[tailrec]
  theorem same: n = n := rfl
  n
