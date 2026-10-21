-- Sorting from the library: `List.sort` (ascending, by the elements' `Ord`:
-- numbers, texts, lists, pairs, …), `List.sortBy` (by a comparison) and
-- `List.sortWith` (by a "may come before" test), with proofs that the result
-- is sorted and a permutation of the input.

theorem sortsNumbers: List.sort [5, 3, 9, 1, 3, 0, 7] = [0, 1, 3, 3, 5, 7, 9] := rfl

theorem sortsEmpty: List.sort ([]: List Nat) = [] := rfl

theorem sortsDot: [2, 1].sort = [1, 2] := rfl

-- Descending, by flipping the test.
theorem sortsDescending: List.sortWith (x y => Nat.leq y x) [1, 3, 2] = [3, 2, 1] := rfl

-- By a key. The sort is stable: pairs with equal keys keep their order.
def byKey (p: Pair Nat Text) (q: Pair Nat Text): Ordering := Nat.compare p.fst q.fst

test "sorts by key, stably" :=
  List.map Pair.snd (List.sortBy byKey [(2, "b"), (1, "x"), (2, "a"), (0, "z"), (1, "y")])
    == ["z", "x", "y", "b", "a"]

test "sorts texts" := List.sortBy Text.compare ["pear", "apple", "fig"] == ["apple", "fig", "pear"]

test "sorts many numbers" :=
  ((List.range 300).map (i => (i * 7919 + 13) % 1009)).sort
    == ((List.range 300).map (i => (i * 7919 + 13) % 1009)).reverse.sortWith Nat.leq

-- Using the theorems.

-- In a sorted list, the first element is at most the second.
theorem firstLeSecond (x: Nat) (y: Nat) (rest: List Nat):
    List.Sorted Nat.leq (Cons x (Cons y rest)) -> x <= y
  | Both h s => h

-- Sorting keeps every element, so it keeps the number of 3s, and the length.
theorem keepsThrees (xs: List Nat): (xs.sort).occurrences (Nat.equal 3) = xs.occurrences (Nat.equal 3) := List.sortPerm xs (Nat.equal 3)

theorem keepsLength (xs: List Nat): (xs.sort).length = xs.length := (xs.sort).permLength xs (xs.sortPerm)

-- `List.sortBy` is sorted given a total comparison; `Nat.compare` on keys is.
theorem byKeySorted (ps: List (Pair Nat Text)): List.Sorted (p q => Ordering.isLessEq (byKey p q)) (ps.sortBy byKey) := ps.sortBySorted byKey (p q => Nat.compareTotal p.fst q.fst)
