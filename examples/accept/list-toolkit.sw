-- The list toolkit and Nat helpers of the library (`List.map`, `Nat.pow`, ...),
-- most of them also by dot notation.


theorem mapped : [1, 2, 3].map (\x -> x + 1) = [2, 3, 4]
mapped = rfl

theorem filtered : [1, 2, 3, 4].filter (\x -> Nat.leq x 2) = [1, 2]
filtered = rfl

theorem folded : [1, 2, 3].foldl (\acc x -> acc * 10 + x) 0 = 123
folded = rfl

theorem foldedRight : [1, 2, 3].foldr (\x acc -> acc * 10 + x) 0 = 321
foldedRight = rfl

theorem summed : [1, 2, 3, 4].sum = 10
summed = rfl

theorem producted : [1, 2, 3, 4].product = 24
producted = rfl

theorem productEmpty : List.product [] = 1
productEmpty = rfl

theorem maximumOf : [3, 9, 2].maximum = Just 9
maximumOf = rfl

theorem minimumOf : [3, 9, 2].minimum = Just 2
minimumOf = rfl

theorem maximumEmpty : List.maximum [] = Nothing
maximumEmpty = rfl

theorem minimumEmpty : List.minimum [] = Nothing
minimumEmpty = rfl

theorem zipped : [1, 2, 3].zip [4, 5] = [MkPair 1 4, MkPair 2 5]
zipped = rfl

theorem zippedWith : [1, 2, 3].zipWith (\x y -> x + y) [10, 20, 30] = [11, 22, 33]
zippedWith = rfl

theorem taken : [1, 2, 3].take 2 = [1, 2]
taken = rfl

theorem takenMore : [1, 2].take 5 = [1, 2]
takenMore = rfl

theorem dropped : [1, 2, 3].drop 2 = [3]
dropped = rfl

theorem droppedMore : [1, 2].drop 5 = []
droppedMore = rfl

theorem got : [5, 6, 7].get 1 = Just 6
got = rfl

theorem gotMissing : [5, 6, 7].get 3 = Nothing
gotMissing = rfl

test "any" = [1, 2, 3].any (\x -> Nat.equal x 2)
test "all" = [1, 2, 3].all (\x -> Nat.leq x 3)
test "not all" = Bool.not ([1, 2, 3].all (\x -> Nat.leq x 2))
test "count" = [1, 2, 3, 4].count (\x -> Nat.leq 3 x) == 2

theorem found : [1, 2, 3].find (\x -> Nat.leq 2 x) = Just 2
found = rfl

theorem notFound : [1, 2, 3].find (\x -> Nat.leq 9 x) = Nothing
notFound = rfl

theorem mappedMaybe : [1, 2, 3, 4].mapMaybe (\x -> if Nat.leq 3 x then Just (x * 2) else Nothing) = [6, 8]
mappedMaybe = rfl

theorem concatenated : [[1], [], [2, 3]].concat = [1, 2, 3]
concatenated = rfl

theorem concatMapped : [1, 2].concatMap (\x -> [x, x]) = [1, 1, 2, 2]
concatMapped = rfl

theorem replicated : List.replicate 3 7 = [7, 7, 7]
replicated = rfl

theorem ranged : List.range 4 = [0, 1, 2, 3]
ranged = rfl

theorem rangedZero : List.range 0 = []
rangedZero = rfl

theorem reversed : [1, 2, 3].reverse = [3, 2, 1]
reversed = rfl

theorem lasted : [1, 2, 3].last = Just 3
lasted = rfl

theorem lastedEmpty : List.last ([] : List Nat) = Nothing
lastedEmpty = rfl

test "elem" = List.elem Nat.decEq 2 [1, 2, 3]
test "not elem" = Bool.not (List.elem Nat.decEq 5 [1, 2, 3])

theorem partitioned : [1, 2, 3, 4].partition (\x -> Nat.leq x 2) = MkPair [1, 2] [3, 4]
partitioned = rfl

theorem looked : List.lookup Nat.decEq 2 [MkPair 1 10, MkPair 2 20] = Just 20
looked = rfl

theorem lookedMissing : List.lookup Nat.decEq 3 [MkPair 1 10, MkPair 2 20] = Nothing
lookedMissing = rfl

test "min" = Nat.min 3 5 == 3
test "max" = Nat.max 3 5 == 5
test "absDiff" = Nat.absDiff 3 10 == 7
test "absDiff flipped" = Nat.absDiff 10 3 == 7
test "pow" = Nat.pow 2 10 == 1024
test "pow zero" = Nat.pow 7 0 == 1

-- Lists compare with `==` too (as the theorems above do with `rfl`).
test "map" = [1, 2, 3].map (\x -> x + 1) == [2, 3, 4]
test "filter" = [1, 2, 3, 4].filter (\x -> Nat.leq x 2) == [1, 2]
test "zip" = [1, 2, 3].zip [4, 5] == [MkPair 1 4, MkPair 2 5]
test "partition" = [1, 2, 3, 4].partition (\x -> Nat.leq x 2) == MkPair [1, 2] [3, 4]
test "maximum" = [3, 9, 2].maximum == Just 9
