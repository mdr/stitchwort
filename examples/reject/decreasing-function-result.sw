-- expect-error: E-DECREASING
-- The function passed to `List.map` returns a function, so `List.mapCong`
-- would compare functions, which needs function extensionality.
import Std (List, Nat)

def offsets (n: Nat): Nat
  decreasing n
:=
  List.sum (List.map (List.map (List.range n) (d => (m => if h: d < n then offsets d + m else m))) ((g: Nat -> Nat) => g 1))
