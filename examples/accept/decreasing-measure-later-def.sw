-- A `decreasing` measure may name a definition declared further down, as a
-- body can: the definition is checked first, since the measure depends on it.
import Std (Nat)

def countDown (n: Nat): Nat
    decreasing (sizeOf n)
:= match n with
  | Zero => 0
  | Succ k => countDown k

def sizeOf (n: Nat): Nat := n
