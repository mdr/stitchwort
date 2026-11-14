--| Tests for `NonEmptyList`.

def NonEmptyList.example: NonEmptyList Nat := { head = 3, tail = [1, 4, 1, 5] }

test "NonEmptyList.toList, length, singleton, cons" :=
  NonEmptyList.example.toList == [3, 1, 4, 1, 5]
    ∧ NonEmptyList.example.length == 5
    ∧ (NonEmptyList.singleton 7).toList == [7]
    ∧ (NonEmptyList.cons 1 [2, 3]).toList == [1, 2, 3]

test "NonEmptyList.count" := NonEmptyList.example.count (x => x > 2) == 3

test "NonEmptyList ==" :=
  NonEmptyList.example == { head = 3, tail = [1, 4, 1, 5] } ∧ NonEmptyList.example != NonEmptyList.singleton 3

test "NonEmptyList show" := "${NonEmptyList.example}" == "[3, 1, 4, 1, 5]"

test "NonEmptyList.reduce, foldLeft, foldRight" :=
  NonEmptyList.example.reduce Nat.add == 14
    ∧ NonEmptyList.singleton 9 |> .reduce Nat.add == 9
    ∧ ({ head = 10, tail = [3, 2] }: NonEmptyList Nat).reduce Nat.sub == 5
    ∧ NonEmptyList.example.foldLeft 0 Nat.add == 14
    ∧ ({ head = 1, tail = [2, 3] }: NonEmptyList Nat).foldRight 0 (x acc => acc * 10 + x) == 321

test "NonEmptyList.last, init" :=
  NonEmptyList.example.last == 5
    ∧ (NonEmptyList.singleton 2).last == 2
    ∧ NonEmptyList.example.init == [3, 1, 4, 1]
    ∧ (NonEmptyList.singleton 2).init == []

test "NonEmptyList.get, getOr" :=
  NonEmptyList.example.get 2 == Some 4
    ∧ NonEmptyList.example.get 5 == None
    ∧ NonEmptyList.example.getOr 2 0 == 4
    ∧ NonEmptyList.example.getOr 9 0 == 0

test "NonEmptyList.maximum, minimum" :=
  NonEmptyList.example.maximum == 5 ∧ NonEmptyList.example.minimum == 1 ∧ (NonEmptyList.singleton 0).maximum == 0

test "NonEmptyList.maxBy, minBy: the first wins a tie" :=
  ({ head = (1, "a"), tail = [(3, "b"), (3, "c"), (0, "d"), (0, "e")] }: NonEmptyList (Pair Nat Text)).maxBy Pair.fst
    == (3, "b")
    ∧ ({ head = (1, "a"), tail = [(3, "b"), (3, "c"), (0, "d"), (0, "e")] }: NonEmptyList (Pair Nat Text)).minBy
        Pair.fst
      == (0, "d")

test "NonEmptyList.maximumOf, minimumOf" :=
  NonEmptyList.example.maximumOf (x => x * 2) == 10 ∧ NonEmptyList.example.minimumOf (x => 10 - x) == 5

test "NonEmptyList.map, zip, zipWith" :=
  (NonEmptyList.example.map (x => x + 1)).toList == [4, 2, 5, 2, 6]
    ∧ (NonEmptyList.example.zip { head = "a", tail = ["b"] }).toList == [(3, "a"), (1, "b")]
    ∧ (NonEmptyList.example.zipWith NonEmptyList.example Nat.add).toList == [6, 2, 8, 2, 10]

test "NonEmptyList.flatMap" := NonEmptyList.example.flatMap (x => [x, x * 10]) == [3, 30, 1, 10, 4, 40, 1, 10, 5, 50]

test "NonEmptyList.sumBy" := NonEmptyList.example.sumBy (x => x * 2) == 28

test "NonEmptyList.reverse" :=
  NonEmptyList.example.reverse.toList == [5, 1, 4, 1, 3] ∧ (NonEmptyList.singleton 1).reverse.toList == [1]

test "NonEmptyList.append, appendList, prependList" :=
  (NonEmptyList.example.append (NonEmptyList.singleton 9)).toList == [3, 1, 4, 1, 5, 9]
    ∧ (NonEmptyList.singleton 1 |> .appendList []).toList == [1]
    ∧ (NonEmptyList.singleton 1 |> .appendList [2]).toList == [1, 2]
    ∧ (NonEmptyList.prependList [7, 8] (NonEmptyList.singleton 1)).toList == [7, 8, 1]
    ∧ (NonEmptyList.prependList [] (NonEmptyList.singleton 1)).toList == [1]

test "NonEmptyList.sort, sortBy: stable" :=
  NonEmptyList.example.sort.toList == [1, 1, 3, 4, 5]
    ∧ (NonEmptyList.example.sortBy (x y => Nat.compare y x)).toList == [5, 4, 3, 1, 1]
    ∧ (({ head = (2, "a"), tail = [(1, "b"), (2, "c"), (1, "d")] }: NonEmptyList (Pair Nat Text)).sortBy (x y =>
      Nat.compare x.fst y.fst)).toList
      == [(1, "b"), (1, "d"), (2, "a"), (2, "c")]

test "NonEmptyList.contains, any, all" :=
  NonEmptyList.example.contains 4
    ∧ !NonEmptyList.example.contains 9
    ∧ NonEmptyList.example.any (x => x > 4)
    ∧ !NonEmptyList.example.any (x => x > 5)
    ∧ NonEmptyList.example.all (x => x > 0)
    ∧ !NonEmptyList.example.all (x => x > 1)

test "List.toNonEmpty, List.nonEmpty" :=
  ([1, 2, 3].toNonEmpty).toList == [1, 2, 3]
    ∧ ([1, 2, 3].nonEmpty == Some { head = 1, tail = [2, 3] })
    ∧ (([]: List Nat).nonEmpty == None)
