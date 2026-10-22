-- `==` on lists, pairs (tuples) and `Option`, whenever their elements have
-- `==`: their `DecEq` instances ask for the elements' instance.

import Std (Bool, Int, List, Nat)

test "lists of numbers" := [1, 2, 3] == [1, 2, 3]
test "different lengths" := !([1, 2, 3] == [1, 2])
test "different elements" := !([1, 2, 3] == [1, 5, 3])
test "empty lists" := List.filter (x => Nat.leq x 0) [1, 2] == []
test "lists of lists" := [[1], [], [2, 3]] == [[1], [], [2, 3]]
test "lists of lists, different" := !([[1], [2, 3]] == [[1], [3, 2]])
test "lists of texts" := ["ab", "", "c"] == ["ab", "", "c"]
test "lists of texts, different" := !(["ab"] == ["abc"])
test "lists of booleans" := [True, False] == [True, False]

test "pairs" := (1, "one") == (1, "one")
test "pairs, first differs" := !((1, "one") == (2, "one"))
test "pairs, second differs" := !((1, "one") == (1, "uno"))
test "triples" := (1, True, "x") == (1, True, "x")
test "triples, last differs" := !((1, True, "x") == (1, True, "y"))

test "Option Int" := Some (Int.neg 3) == Some (Int.neg 3)
test "Option Int, different" := !(Some (Int.neg 3) == Some 3)
test "None and Some" := !(Some (Int.neg 3) == None)
test "None" := List.maximum ([]: List Nat) == None

test "nested" := [Some (1, ["a"]), None] == [Some (1, ["a"]), None]
test "nested, different" := !([Some (1, ["a"]), None] == [Some (1, ["b"]), None])
test "zip" := [1, 2].zip ["a", "b"] == [(1, "a"), (2, "b")]

-- In a definition, too, not just at compile time.
def sameShape (xs: List (Option Nat)) (ys: List (Option Nat)): Bool := xs == ys

test "at run time" := sameShape [Some 1, None] [Some 1, None]
test "at run time, different" := !(sameShape [Some 1] [Some 2])

-- A record whose fields are a list, a tuple and a `Option` gets `==` too.
type Entry = { ids: List Nat, pair: (Nat, Text), delta: Option Int }

def entry: Entry := { ids = [1, 2], pair = (3, "x"), delta = Some (Int.neg 4) }

test "record with containers" := entry == { ids = [1, 2], pair = (3, "x"), delta = Some (Int.neg 4) }
test "record, list differs" := !(entry == { entry | ids = [2, 1] })
test "record, tuple differs" := !(entry == { entry | pair = (3, "y") })
test "record, Option differs" := !(entry == { entry | delta = None })

-- A record with a record field gets `==` too.
type Tagged = { tag: Text, entry: Entry }

def tagged: Tagged := { tag = "t", entry = entry }

test "nested record" := tagged == { tag = "t", entry = entry }
test "nested record, inner field differs" := !(tagged == { tagged | entry = { entry | ids = [] } })
test "nested record, outer field differs" := !(tagged == { tagged | tag = "u" })
