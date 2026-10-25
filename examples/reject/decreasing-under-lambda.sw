-- expect-error: E-DECREASING
-- A recursive call inside a function passed to another needs its proof that
-- the measure is smaller like any other, and nothing in scope says `d < n`:
-- the message shows the goal, and suggests the guard.
import Std (List, Nat)

def weight (n: Nat): Nat
  decreasing n
:=
  1 + List.sum (List.map (List.range n) (d => weight d))
