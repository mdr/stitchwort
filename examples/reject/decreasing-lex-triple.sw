-- expect-error: E-DECREASING
-- A lexicographic measure is a pair; a pair inside it (three measures) isn't
-- supported yet.
import Std (Nat)

def countDown (a: Nat) (b: Nat) (c: Nat): Nat
    decreasing (a, (b, c))
:=
  match c with
    | Zero => 0
    | Succ k => countDown a b k [decreasing := omega]
