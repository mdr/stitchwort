-- `Map` and `Set` keep their keys in order, so listing them is predictable.
-- They are not in the prelude: import them.
import Std (Map, Nat, Set)

-- Count words: `Map.counts` does it in one call.
def wordCounts (words: List Text): Map Text Nat := Map.counts words

test "counting" := (wordCounts ["b", "a", "b"]).toList == [("a", 1), ("b", 2)]
test "lookup" := (wordCounts ["b", "a", "b"]).get "b" == Some 2
test "a missing key" := (wordCounts ["a"]).getOr 0 "z" == 0

-- Update with `insertWith`, which says how to combine with an old value.
def tally (m: Map Text Nat) (word: Text): Map Text Nat := m.insertWith Nat.add word 1

test "insertWith" := (["x", "x"].foldLeft tally Map.empty).get "x" == Some 2

-- A set of positions a walk visits, ordered by row, then column.
def visited: Set (Nat, Nat) := Set.fromList [(0, 0), (0, 1), (1, 1), (0, 1)]

test "no duplicates" := visited.size == 3
test "membership" := visited.contains (1, 1) && !visited.contains (1, 0)

-- Two maps with the same entries are equal, however they were made.
test "equal maps" := Map.fromList [("a", 1), ("b", 2)] == Map.fromList [("b", 2), ("a", 1)]
