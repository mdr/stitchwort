-- A lambda whose parameter type comes from a later argument is still checked
-- last when a later parameter's type, or the result's, mentions it (SW-138):
-- `List.anyPerm xs ys h (r => r.contains 3)` (the result mentions the
-- predicate), and `List.sortBySorted (a b => …) (a b => …) xs` (the second
-- lambda's type mentions the first, and both wait for `xs`).

import Std (List, Nat, Ordering)

type R = { lo: Nat, hi: Nat }

def R.contains (r: R) (n: Nat): Bool := Nat.leq r.lo n

theorem anyPermLam (xs: List R) (ys: List R) (h: List.Perm xs ys): List.any xs (r => r.contains 3) = List.any ys (r => r.contains 3) :=
  List.anyPerm xs ys h (r => r.contains 3)

theorem sortedLam (xs: List R): List.Sorted (x y => Ordering.isLessEq (Nat.compare x.lo y.lo)) (List.sortBy xs (a b => Nat.compare a.lo b.lo)) :=
  List.sortBySorted (a b => Nat.compare a.lo b.lo) (a b => Nat.compareTotal a.lo b.lo) xs
