-- `==` on lists, pairs (tuples) and `Maybe`, whenever their elements have
-- `==`: `List.decEq`, `Pair.decEq` and `Maybe.decEq` take a decision
-- procedure for the elements, and `auto` finds it.

test "lists of numbers" := [1, 2, 3] == [1, 2, 3]
test "different lengths" := Bool.not ([1, 2, 3] == [1, 2])
test "different elements" := Bool.not ([1, 2, 3] == [1, 5, 3])
test "empty lists" := List.filter (\x => Nat.leq x 0) [1, 2] == []
test "lists of lists" := [[1], [], [2, 3]] == [[1], [], [2, 3]]
test "lists of lists, different" := Bool.not ([[1], [2, 3]] == [[1], [3, 2]])
test "lists of texts" := ["ab", "", "c"] == ["ab", "", "c"]
test "lists of texts, different" := Bool.not (["ab"] == ["abc"])
test "lists of booleans" := [True, False] == [True, False]

test "pairs" := (1, "one") == (1, "one")
test "pairs, first differs" := Bool.not ((1, "one") == (2, "one"))
test "pairs, second differs" := Bool.not ((1, "one") == (1, "uno"))
test "triples" := (1, True, "x") == (1, True, "x")
test "triples, last differs" := Bool.not ((1, True, "x") == (1, True, "y"))

test "Maybe Int" := Just (Int.neg 3) == Just (Int.neg 3)
test "Maybe Int, different" := Bool.not (Just (Int.neg 3) == Just 3)
test "Nothing and Just" := Bool.not (Just (Int.neg 3) == Nothing)
test "Nothing" := List.maximum [] == Nothing

test "nested" := [Just (1, ["a"]), Nothing] == [Just (1, ["a"]), Nothing]
test "nested, different" := Bool.not ([Just (1, ["a"]), Nothing] == [Just (1, ["b"]), Nothing])
test "zip" := [1, 2].zip ["a", "b"] == [(1, "a"), (2, "b")]

-- In a definition, too, not just at compile time.
def sameShape (xs : List (Maybe Nat)) (ys : List (Maybe Nat)) : Bool := xs == ys

test "at run time" := sameShape [Just 1, Nothing] [Just 1, Nothing]
test "at run time, different" := Bool.not (sameShape [Just 1] [Just 2])

-- A record whose fields are a list, a tuple and a `Maybe` gets `==` too.
type Entry = { ids : List Nat, pair : (Nat, Text), delta : Maybe Int }

def entry : Entry := { ids = [1, 2], pair = (3, "x"), delta = Just (Int.neg 4) }

test "record with containers" := entry == { ids = [1, 2], pair = (3, "x"), delta = Just (Int.neg 4) }
test "record, list differs" := Bool.not (entry == { entry | ids = [2, 1] })
test "record, tuple differs" := Bool.not (entry == { entry | pair = (3, "y") })
test "record, Maybe differs" := Bool.not (entry == { entry | delta = Nothing })
