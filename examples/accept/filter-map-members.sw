-- `filterMap` with callbacks that only need to behave on the list's own
-- elements: two that agree there give the same list, one that keeps every
-- element changed is a `map`, and one that keeps every element as it is
-- gives the list back.
import Std (List, Nat)

-- The number before `n`, if there is one.
def predecessor (n: Nat): Option Nat := if n == 0 then None else Some (n - 1)

-- Keeps numbers below a limit.
def below (limit: Nat) (n: Nat): Option Nat := if n < limit then Some n else None

def successors (xs: List Nat): List Nat := xs.map Succ

test "predecessors" := [0, 1, 2].filterMap predecessor == [0, 1]

-- On successors `predecessor` always keeps, so there it agrees with `Some`
-- of the number before (though not on 0).
theorem predecessorsOfSuccessors (xs: List Nat):
    (successors xs).filterMap predecessor = (successors xs).filterMap (n => Some (n - 1)) :=
  List.filterMapCongMem (successors xs) predecessor (n => Some (n - 1)) (n m =>
    List.anyElim (x => Succ x = n) (predecessor n = Some (n - 1)) xs (List.memMapAny xs Succ n m)
      (x inXs e => rewrite <- e in rfl))

-- And so it is a `map`.
theorem predecessorsOfSuccessorsMap (xs: List Nat): (successors xs).filterMap predecessor = (successors xs).map (n => n - 1) :=
  List.filterMapSomeMem (successors xs) predecessor (n => n - 1) (n m =>
    List.anyElim (x => Succ x = n) (predecessor n = Some (n - 1)) xs (List.memMapAny xs Succ n m)
      (x inXs e => rewrite <- e in rfl))

-- A limit above every element keeps the whole list.
theorem belowKeepsRange (n: Nat): (List.range n).filterMap (below n) = List.range n :=
  List.filterMapAll (below n) (List.range n) (x m =>
    rewrite And.right (List.memRangeFrom x n 0 m) in rfl)
