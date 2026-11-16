-- The list toolkit and Nat helpers of the library (`List.map`, `Nat.pow`, ...),
-- most of them also by dot notation.

import Std (Bool, List, Nat)

theorem mapped: [1, 2, 3].map (x => x + 1) = [2, 3, 4] := byComputing

theorem filtered: [1, 2, 3, 4].filter (x => Nat.leq x 2) = [1, 2] := byComputing

theorem folded: [1, 2, 3].foldLeft 0 (acc x => acc * 10 + x) = 123 := byComputing

theorem scanned: [1, 2, 3].scanLeft 0 (acc x => acc + x) = [0, 1, 3, 6] := byComputing

theorem foldedRight: [1, 2, 3].foldRight 0 (x acc => acc * 10 + x) = 321 := byComputing

theorem summed: [1, 2, 3, 4].sum = 10 := byComputing

theorem producted: [1, 2, 3, 4].product = 24 := byComputing

theorem productEmpty: List.product [] = 1 := byComputing

theorem maximumOf: [3, 9, 2].maximum = Some 9 := byComputing

theorem minimumOf: [3, 9, 2].minimum = Some 2 := byComputing

theorem maximumEmpty: List.maximum ([]: List Nat) = None := byComputing

theorem minimumEmpty: List.minimum ([]: List Nat) = None := byComputing

theorem zipped: [1, 2, 3].zip [4, 5] = [MkPair 1 4, MkPair 2 5] := byComputing

theorem zippedWith: [1, 2, 3].zipWith [10, 20, 30] (x y => x + y) = [11, 22, 33] := byComputing

theorem zippedWith3: [1, 2, 3].zipWith3 [10, 20, 30] [100, 200, 300] (x y z => x + y + z) = [111, 222, 333] :=
  byComputing

theorem zippedWith3ShortFirst: ([]: List Nat).zipWith3 [10, 20] [100, 200] (x y z => x + y + z) = [] := byComputing

theorem zippedWith3ShortMiddle: [1, 2].zipWith3 [10] [100, 200] (x y z => x + y + z) = [111] := byComputing

theorem zippedWith3ShortLast: [1, 2].zipWith3 [10, 20] [100] (x y z => x + y + z) = [111] := byComputing

theorem zippedWith3Empty: ([]: List Nat).zipWith3 ([]: List Nat) ([]: List Nat) (x y z => x + y + z) = [] := byComputing

theorem taken: [1, 2, 3].take 2 = [1, 2] := byComputing

theorem takenMore: [1, 2].take 5 = [1, 2] := byComputing

theorem dropped: [1, 2, 3].drop 2 = [3] := byComputing

theorem droppedMore: [1, 2].drop 5 = [] := byComputing

theorem got: [5, 6, 7].get 1 = Some 6 := byComputing

theorem gotMissing: [5, 6, 7].get 3 = None := byComputing

test "any" := [1, 2, 3].any (x => Nat.equal x 2)
test "all" := [1, 2, 3].all (x => Nat.leq x 3)
test "not all" := ¬([1, 2, 3].all (x => Nat.leq x 2))
test "count" := [1, 2, 3, 4].count (x => Nat.leq 3 x) == 2

theorem found: [1, 2, 3].find (x => Nat.leq 2 x) = Some 2 := byComputing

theorem notFound: [1, 2, 3].find (x => Nat.leq 9 x) = None := byComputing

theorem mappedOption: [1, 2, 3, 4].filterMap (x => if Nat.leq 3 x then Some (x * 2) else None) = [6, 8] := byComputing

theorem concatenated: [[1], [], [2, 3]].concat = [1, 2, 3] := byComputing

theorem concatMapped: [1, 2].concatMap (x => [x, x]) = [1, 1, 2, 2] := byComputing

theorem replicated: List.replicate 3 7 = [7, 7, 7] := byComputing

theorem ranged: List.range 0 4 = [0, 1, 2, 3] := byComputing

theorem rangedZero: List.range 0 0 = [] := byComputing

theorem reversed: [1, 2, 3].reverse = [3, 2, 1] := byComputing

theorem lasted: [1, 2, 3].last = Some 3 := byComputing

theorem lastedEmpty: ([]: List Nat).last = None := byComputing

test "elem" := List.elem [1, 2, 3] 2 Nat.decEq
test "not elem" := ¬(List.elem [1, 2, 3] 5 Nat.decEq)

theorem partitioned: [1, 2, 3, 4].partition (x => Nat.leq x 2) = MkPair [1, 2] [3, 4] := byComputing

theorem looked: List.lookup [MkPair 1 10, MkPair 2 20] 2 = Some 20 := byComputing

theorem lookedMissing: List.lookup [MkPair 1 10, MkPair 2 20] 3 = None := byComputing

test "min" := Nat.min 3 5 == 3
test "max" := Nat.max 3 5 == 5
test "absDiff" := Nat.absDiff 3 10 == 7
test "absDiff flipped" := Nat.absDiff 10 3 == 7
test "pow" := Nat.pow 2 10 == 1024
test "pow zero" := Nat.pow 7 0 == 1

-- Lists compare with `==` too (as the theorems above do with `byComputing`).
test "map" := [1, 2, 3].map (+ 1) == [2, 3, 4]
test "filter" := [1, 2, 3, 4].filter (x => Nat.leq x 2) == [1, 2]
test "zip" := [1, 2, 3].zip [4, 5] == [MkPair 1 4, MkPair 2 5]
test "partition" := [1, 2, 3, 4].partition (x => Nat.leq x 2) == MkPair [1, 2] [3, 4]
test "maximum" := [3, 9, 2].maximum == Some 9
