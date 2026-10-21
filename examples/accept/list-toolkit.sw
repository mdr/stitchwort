-- The list toolkit and Nat helpers of the library (`List.map`, `Nat.pow`, ...),
-- most of them also by dot notation.

import Std (Bool, List, Nat)

theorem mapped: [1, 2, 3].map (x => x + 1) = [2, 3, 4] := rfl

theorem filtered: [1, 2, 3, 4].filter (x => Nat.leq x 2) = [1, 2] := rfl

theorem folded: [1, 2, 3].foldLeft (acc x => acc * 10 + x) 0 = 123 := rfl

theorem scanned: [1, 2, 3].scanLeft (acc x => acc + x) 0 = [0, 1, 3, 6] := rfl

theorem foldedRight: [1, 2, 3].foldRight (x acc => acc * 10 + x) 0 = 321 := rfl

theorem summed: [1, 2, 3, 4].sum = 10 := rfl

theorem producted: [1, 2, 3, 4].product = 24 := rfl

theorem productEmpty: List.product [] = 1 := rfl

theorem maximumOf: [3, 9, 2].maximum = Some 9 := rfl

theorem minimumOf: [3, 9, 2].minimum = Some 2 := rfl

theorem maximumEmpty: List.maximum ([]: List Nat) = None := rfl

theorem minimumEmpty: List.minimum ([]: List Nat) = None := rfl

theorem zipped: [1, 2, 3].zip [4, 5] = [MkPair 1 4, MkPair 2 5] := rfl

theorem zippedWith: [1, 2, 3].zipWith (x y => x + y) [10, 20, 30] = [11, 22, 33] := rfl

theorem zippedWith3: [1, 2, 3].zipWith3 (x y z => x + y + z) [10, 20, 30] [100, 200, 300] = [111, 222, 333] := rfl

theorem zippedWith3ShortFirst: ([]: List Nat).zipWith3 (x y z => x + y + z) [10, 20] [100, 200] = [] := rfl

theorem zippedWith3ShortMiddle: [1, 2].zipWith3 (x y z => x + y + z) [10] [100, 200] = [111] := rfl

theorem zippedWith3ShortLast: [1, 2].zipWith3 (x y z => x + y + z) [10, 20] [100] = [111] := rfl

theorem zippedWith3Empty: ([]: List Nat).zipWith3 (x y z => x + y + z) ([]: List Nat) ([]: List Nat) = [] := rfl

theorem taken: [1, 2, 3].take 2 = [1, 2] := rfl

theorem takenMore: [1, 2].take 5 = [1, 2] := rfl

theorem dropped: [1, 2, 3].drop 2 = [3] := rfl

theorem droppedMore: [1, 2].drop 5 = [] := rfl

theorem got: [5, 6, 7].get 1 = Some 6 := rfl

theorem gotMissing: [5, 6, 7].get 3 = None := rfl

test "any" := [1, 2, 3].any (x => Nat.equal x 2)
test "all" := [1, 2, 3].all (x => Nat.leq x 3)
test "not all" := Bool.not ([1, 2, 3].all (x => Nat.leq x 2))
test "count" := [1, 2, 3, 4].count (x => Nat.leq 3 x) == 2

theorem found: [1, 2, 3].find (x => Nat.leq 2 x) = Some 2 := rfl

theorem notFound: [1, 2, 3].find (x => Nat.leq 9 x) = None := rfl

theorem mappedOption: [1, 2, 3, 4].filterMap (x => if Nat.leq 3 x then Some (x * 2) else None) = [6, 8] := rfl

theorem concatenated: [[1], [], [2, 3]].concat = [1, 2, 3] := rfl

theorem concatMapped: [1, 2].concatMap (x => [x, x]) = [1, 1, 2, 2] := rfl

theorem replicated: List.replicate 3 7 = [7, 7, 7] := rfl

theorem ranged: List.range 4 = [0, 1, 2, 3] := rfl

theorem rangedZero: List.range 0 = [] := rfl

theorem reversed: [1, 2, 3].reverse = [3, 2, 1] := rfl

theorem lasted: [1, 2, 3].last = Some 3 := rfl

theorem lastedEmpty: ([]: List Nat).last = None := rfl

test "elem" := List.elem Nat.decEq 2 [1, 2, 3]
test "not elem" := Bool.not (List.elem Nat.decEq 5 [1, 2, 3])

theorem partitioned: [1, 2, 3, 4].partition (x => Nat.leq x 2) = MkPair [1, 2] [3, 4] := rfl

theorem looked: List.lookup Nat.decEq 2 [MkPair 1 10, MkPair 2 20] = Some 20 := rfl

theorem lookedMissing: List.lookup Nat.decEq 3 [MkPair 1 10, MkPair 2 20] = None := rfl

test "min" := Nat.min 3 5 == 3
test "max" := Nat.max 3 5 == 5
test "absDiff" := Nat.absDiff 3 10 == 7
test "absDiff flipped" := Nat.absDiff 10 3 == 7
test "pow" := Nat.pow 2 10 == 1024
test "pow zero" := Nat.pow 7 0 == 1

-- Lists compare with `==` too (as the theorems above do with `rfl`).
test "map" := [1, 2, 3].map (x => x + 1) == [2, 3, 4]
test "filter" := [1, 2, 3, 4].filter (x => Nat.leq x 2) == [1, 2]
test "zip" := [1, 2, 3].zip [4, 5] == [MkPair 1 4, MkPair 2 5]
test "partition" := [1, 2, 3, 4].partition (x => Nat.leq x 2) == MkPair [1, 2] [3, 4]
test "maximum" := [3, 9, 2].maximum == Some 9
