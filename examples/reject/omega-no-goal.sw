-- expect-error: E-ARITHMETIC
-- With no expected type, `arithmetic` does not know what to prove.
import Std (Nat)

def f (x: Nat): Nat :=
  let p := arithmetic
  x
