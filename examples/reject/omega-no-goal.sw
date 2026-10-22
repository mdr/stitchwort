-- expect-error: E-OMEGA
-- With no expected type, `omega` does not know what to prove.
import Std (Nat)

def f (x: Nat): Nat :=
  let p := omega
  x
