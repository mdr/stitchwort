-- expect-error: E-DECREASING
-- A recursive call inside a function passed to another has no proof that
-- its argument is smaller: stage 1 refuses it.
import Std (List, Nat)

def weight (n: Nat): Nat
  decreasing n
:=
  1 + List.sum (List.map (d => weight d) (List.range n))
