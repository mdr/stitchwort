-- expect-error: E-DECREASING
-- `total` has no congruence lemma (`totalCong`), so `decreasing` can't show
-- that it gives the same result for two functions that agree everywhere:
-- the message says which lemma, and its shape.
import Std (List, Nat)

def total (f: Nat → Nat): List Nat → Nat
  | Nil       => 0
  | Cons x xs => f x + total f xs

def weight (n: Nat): Nat
  decreasing n
:=
  1 + total (d => if h: d < n then weight d else 0) (List.range n)
