--| `NonEmptyList (Set k)`: the intersection and union of every set, the
--| intersection starting from the first set.
-- Its own file because Map/Map.sw needs NonEmptyList (for `Map.groupBy`) and
-- Set/Set.sw needs Map/Map.sw.

import Std (Eq)

--| The keys in every set, starting from the first set, so there is no made-up
--| "all keys" to start from: `people.map .answers |> .intersectAll`
--| ([`NonEmptyList.intersectAllReduce`]).
def NonEmptyList.intersectAll [auto ord: Ord k] (sets: NonEmptyList (Set k)): Set k :=
  NonEmptyList.reduce sets Set.intersect

--| The keys in any of the sets ([`NonEmptyList.unionAllReduce`]).
def NonEmptyList.unionAll [auto ord: Ord k] (sets: NonEmptyList (Set k)): Set k := NonEmptyList.reduce sets Set.union

theorem NonEmptyList.intersectAllReduce ∀ [auto ord: Ord k] (sets: NonEmptyList (Set k)):
    sets.intersectAll = sets.reduce Set.intersect :=
  rfl

theorem NonEmptyList.unionAllReduce ∀ [auto ord: Ord k] (sets: NonEmptyList (Set k)):
    sets.unionAll = sets.reduce Set.union :=
  rfl

--| The intersection holds what every set holds.
theorem NonEmptyList.containsIntersectAll ∀ [auto ord: Ord k] (sets: NonEmptyList (Set k)) (key: k):
    Set.contains sets.intersectAll key = sets.all (s => Set.contains s key) :=
  Set.containsFoldIntersect key sets.tail sets.head

--| The union holds what some set holds.
theorem NonEmptyList.containsUnionAll ∀ [auto ord: Ord k] (sets: NonEmptyList (Set k)) (key: k):
    Set.contains sets.unionAll key = sets.any (s => Set.contains s key) :=
  Set.containsFoldUnion key sets.tail sets.head

theorem NonEmptyList.singletonIntersectAll ∀ [auto ord: Ord k] (s: Set k):
    (NonEmptyList.singleton s).intersectAll = s :=
  rfl

theorem NonEmptyList.singletonUnionAll ∀ [auto ord: Ord k] (s: Set k): (NonEmptyList.singleton s).unionAll = s := rfl

test "NonEmptyList.intersectAll, unionAll" :=
  let a := Set.fromList [1, 2, 3]
  let b := Set.fromList [2, 3, 4]
  let c := Set.fromList [3, 4, 5]
  ({ head = a, tail = [b, c] }: NonEmptyList (Set Nat)).intersectAll == Set.fromList [3]
    ∧ ({ head = a, tail = [b, c] }: NonEmptyList (Set Nat)).unionAll == Set.fromList [1, 2, 3, 4, 5]
    ∧ (NonEmptyList.singleton a).intersectAll == a
