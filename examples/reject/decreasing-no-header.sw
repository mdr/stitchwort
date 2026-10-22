-- expect-error: E-DECREASING
-- The measure can only use parameters named in the header.
import Std (Nat)

def count: Nat -> Nat
  decreasing 0
  | Zero => 0
  | Succ k => count k
