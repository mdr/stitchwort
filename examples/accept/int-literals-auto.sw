-- Number literals take their type from what's expected, also through a
-- function with an `auto` instance parameter (`Set.fromList [auto ord: Ord k]`):
-- the result type reaches the arguments before the literals would default to
-- `Nat` (SW-248).

import Std (List, Map, Set)

def ints: Set Int := Set.fromList [1, 2, 3]

def zeros: Set Int := Set.fromList [0, 0, 0, 0, 0]

def single: Set Int := Set.fromList [3]

def negatives: Set Int := Set.fromList [3, -1, 2, -5]

def cells: Set (Int, Int) := Set.fromList [(3, 3)]

def moves: Set (Int, Int) := Set.fromList [(0, 1), (1, 0), (-1, 0), (0, -1)]

def named: Map Int Text := Map.fromList [(2, "b"), (-1, "a")]

def pairs: Map (Int, Int) Nat := Map.fromList [((1, -1), 1), ((-2, 0), 2)]

def sorted: List Int := List.sort [3, -1, 2]

test "a set at Int" := ints.toList == [1, 2, 3] ∧ zeros.toList == [0] ∧ single.toList == [3]

test "negatives" := negatives.toList == [-5, -1, 2, 3] ∧ sorted == [-1, 2, 3]

test "tuples" := cells.toList == [(3, 3)] ∧ moves.toList == [(-1, 0), (0, -1), (0, 1), (1, 0)]

test "a map at Int" := named.toList == [(-1, "a"), (2, "b")] ∧ pairs.toList == [((-2, 0), 2), ((1, -1), 1)]

-- Without an expected type a literal is still a `Nat`.
test "defaults" := (Set.fromList [3, 1, 2]).toList == [1, 2, 3]
