-- Maps with the same entries are equal, whatever order they were built in
-- (std/Map/Map.sw, std/Set/Set.sw; docs/proposals/map-equality.md §8). A
-- `Map` is a quotient of its trees by "the same entries in key order", so
-- `=` and `==` on maps mean "the same pairs", and records holding maps
-- derive `==`.

import Std (Bool, Eq, List, Map, Nat, Set)

-- The same entries, inserted in different orders: different trees, the same map.
def forwards: Map Nat Text := Map.fromList [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
def backwards: Map Nat Text := Map.fromList [(4, "d"), (3, "c"), (2, "b"), (1, "a")]

test "insertion order doesn't matter" := forwards == backwards
test "a changed value does" := forwards ≠ backwards.insert 2 "B"
test "an extra key does" := forwards ≠ backwards.insert 5 "e"
test "removing and putting back" := forwards == (forwards.remove 3).insert 3 "c"
test "size is the number of entries" :=
  ((forwards.remove 2).insert 9 "z").size == ((forwards.remove 2).insert 9 "z").toList.length

-- A record with a map in it gets `==`, the map compared by its entries.
type Stock = { owner: Text, counts: Map Text Nat }

def morning: Stock := { owner = "Ada", counts = Map.fromList [("nails", 3), ("screws", 5)] }
def evening: Stock := { owner = "Ada", counts = Map.fromList [("screws", 5)] |> .insert "nails" 3 }

test "records with maps" := morning == evening ∧ morning ≠ { owner = "Bo", counts = evening.counts }

-- Sets: the same keys.
test "sets in any order" := (Set.fromList [3, 1, 2]: Set Nat) == Set.fromList [2, 3, 1, 1]
test "sets differ" := (Set.fromList [1, 2]: Set Nat) ≠ Set.fromList [1, 3]

-- Proofs. `size` counts the entries, for every map.
theorem sizeIsLength (m: Map Text Nat): m.size = m.toList.length := Map.sizeToList m

-- Inserting two different keys in either order gives the same map, for any
-- map, so anything said of one is said of the other.
theorem insertSwap (m: Map Text Nat):
    ((m.insert "a" 1).insert "b" 2) = ((m.insert "b" 2).insert "a" 1) :=
  Map.insertComm "a" 1 "b" 2 (e => Bool.trueNotFalse (Eq.cong (t => t == "a") e)) m

theorem insertSwapSize (m: Map Text Nat):
    ((m.insert "a" 1).insert "b" 2).size = ((m.insert "b" 2).insert "a" 1).size :=
  Eq.cong Map.size (insertSwap m)

-- Maps that agree on every key are equal, even maps of functions, which
-- have no `==`.
theorem functionsExt (m: Map Nat (Nat → Nat)) (n: Map Nat (Nat → Nat)) (h: (key: Nat) → m.get key = n.get key): m = n :=
  Map.ext m n h

-- `filter` keeps the entries for which the test holds, in key order.
theorem filterInOrder (m: Map Nat Nat):
    (m.filter (key value => value > 2)).toList = m.toList.filter (e => e.snd > 2) :=
  Map.toListFilterList m (key value => value > 2)

-- Closed maps: `toList` computes, so `rfl` proves them equal, and `==`
-- computes too.
theorem forwardsBackwards: forwards = backwards := Map.toListInjective forwards backwards rfl

theorem equalByComputing: (forwards == backwards) = True := rfl
