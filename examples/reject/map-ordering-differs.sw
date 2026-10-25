-- expect-error: E-TYPE-MISMATCH
-- The library's `Map` with a named alternative ordering, passed where the
-- parameter's type is `Map Nat Nat`, which means the instance's ordering: the
-- ordering is part of the map's type (docs/proposals/interfaces.md §7.5).

import Std (Eq, Map, Nat, Ord)

def descending: Ord Nat :=
  Ord.fromCompare (x y => Nat.compare y x)
    (x y h => Eq.sym (Nat.compareEqual y x h))
    (x y => Nat.compareFlip y x)
    (x y z h1 h2 => Nat.compareTrans z y x h2 h1)

def total (m: Map Nat Nat): Nat := m.foldLeft 0 (acc key value => acc + value)

def down: Map Nat Nat [ord := descending] := Map.fromList [(1, 10), (2, 20)]

def wrong: Nat := total down
