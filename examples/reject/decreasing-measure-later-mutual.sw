-- expect-error: E-DECREASING
-- A `decreasing` measure that names a definition declared below, which calls
-- the first one: they are checked together, and `decreasing` doesn't support
-- that yet.
import Std (Nat)

def innerN (n: Nat): Nat
    decreasing outerN
:=
  match n with
    | Zero => 0
    | Succ k => outerN k

def outerN (n: Nat): Nat := innerN n
