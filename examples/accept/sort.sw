-- Sorting from the library: `List.sort` (numbers, ascending), `List.sortBy`
-- (by a comparison) and `List.sortWith` (by a "may come before" test), with
-- proofs that the result is sorted and a permutation of the input.

theorem sortsNumbers : List.sort [5, 3, 9, 1, 3, 0, 7] = [0, 1, 3, 3, 5, 7, 9]
sortsNumbers = rfl

theorem sortsEmpty : List.sort [] = []
sortsEmpty = rfl

theorem sortsDot : [2, 1].sort = [1, 2]
sortsDot = rfl

-- Descending, by flipping the test.
theorem sortsDescending : List.sortWith (\x y -> Nat.leq y x) [1, 3, 2] = [3, 2, 1]
sortsDescending = rfl

-- By a key. The sort is stable: pairs with equal keys keep their order.
byKey : Pair Nat Text -> Pair Nat Text -> Ordering
byKey p q = Nat.compare (Pair.fst p) (Pair.fst q)

test "sorts by key, stably" =
  List.map Pair.snd (List.sortBy byKey [(2, "b"), (1, "x"), (2, "a"), (0, "z"), (1, "y")])
    == ["z", "x", "y", "b", "a"]

test "sorts texts" = List.sortBy Text.compare ["pear", "apple", "fig"] == ["apple", "fig", "pear"]

test "sorts many numbers" =
  List.sort (List.map (\i -> (i * 7919 + 13) % 1009) (List.range 300))
    == List.sortWith Nat.leq (List.reverse (List.map (\i -> (i * 7919 + 13) % 1009) (List.range 300)))

-- Using the theorems.

-- In a sorted list, the first element is at most the second.
theorem firstLeSecond : (x : Nat) -> (y : Nat) -> (rest : List Nat) ->
  List.Sorted Nat.leq (Cons x (Cons y rest)) -> x <= y
firstLeSecond x y rest (Both h s) = h

-- Sorting keeps every element, so it keeps the number of 3s, and the length.
theorem keepsThrees : (xs : List Nat) -> List.occurrences (Nat.equal 3) (List.sort xs) = List.occurrences (Nat.equal 3) xs
keepsThrees xs = List.sortPerm xs (Nat.equal 3)

theorem keepsLength : (xs : List Nat) -> List.length (List.sort xs) = List.length xs
keepsLength xs = List.permLength (List.sort xs) xs (List.sortPerm xs)

-- `List.sortBy` is sorted given a total comparison; `Nat.compare` on keys is.
theorem byKeySorted : (ps : List (Pair Nat Text)) -> List.Sorted (\p q -> Ordering.isLessEq (byKey p q)) (List.sortBy byKey ps)
byKeySorted ps = List.sortBySorted byKey (\p q -> Nat.compareTotal (Pair.fst p) (Pair.fst q)) ps
