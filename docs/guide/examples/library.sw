-- Chapter 6: a tour of the standard library.
import Std (Array, Each, List, Map, NonEmptyList, Nat, Option, Result, Set, Text, Vec)
import Std.Each (each)

-- begin lists
def scores: List Nat := [7, 3, 9, 3, 5]

test "map and filter" := (scores.filter (n => n > 4)).map (n => n * 10) == [70, 90, 50]
test "folds" := scores.foldLeft 0 (total n => total + n) == scores.sum
test "searching" := scores.find (n => n > 7) == Some 9 ∧ scores.findIndex (n => n == 9) == Some 2
test "sorting and dedup" := scores.sort.dedup == [3, 5, 7, 9]
test "slicing" := scores.take 2 == [7, 3] ∧ scores.drop 3 == [3, 5]
test "zipping" := List.zipWith [1, 2, 3] [4, 5, 6] (a b => a * b) == [4, 10, 18]
test "ranges" := 0 ..< 4 == [0, 1, 2, 3] ∧ 2 ..= 5 == [2, 3, 4, 5]
test "with an index" := ["a", "b"].withIndex == [(0, "a"), (1, "b")]
test "maximum of an empty list" := ([]: List Nat).maximum == None
-- end lists

-- begin ranges
def squares (n: Nat): List Nat := 0 ..< n |> .map (i => i * i)

test "up to, not including" := 0 ..< 3 == [0, 1, 2]
test "through" := 1 ..= 3 == [1, 2, 3]
test "nothing when the end is below the start" := 5 ..< 2 == []
test "mapping over a range" := squares 4 == [0, 1, 4, 9]
test "range membership" := 3 in 0 ..< 5 ∧ 5 !in 0 ..< 5
test "in a spread" := [0, ..2 ..< 5, 9] == [0, 2, 3, 4, 9]
test "each number of a range" := Each.collect (() => each (1 ..= 3) * 10) == [10, 20, 30]

theorem inRange ∀ (x n: Nat) (h: x < n): x ∈ 0 ..< n := omega

theorem upTo ∀ (x n: Nat) (h: x ∈ 0 ..< n): x < n := omega
-- end ranges

-- begin option
def lookupAge (name: Text): Option Nat := if name == "Ada" then Some 36 else None

test "map" := (lookupAge "Ada").map (age => age + 1) == Some 37
test "getOrElse" := (lookupAge "Bob").getOrElse 0 == 0
test "flatMap" := (lookupAge "Ada").flatMap (age => if age > 18 then Some "adult" else None) == Some "adult"
test "filterMap" := ["1", "x", "3"].filterMap Text.toNat == [1, 3]
-- end option

-- begin result
def parseAge (text: Text): Result Nat Text := match text.toNat with
  | Some age => Ok age
  | None => Err "not a number: '${text}'"

test "ok" := parseAge "36" == Ok 36
test "err" := parseAge "old" == Err "not a number: 'old'"
test "map over Ok" := (parseAge "36").map (age => age * 2) == Ok 72
test "traverse stops at the first Err" := Result.traverse ["1", "x", "y"] parseAge == Err "not a number: 'x'"
-- end result

-- begin text
test "split and join" := Text.join ("a,b,c".split ',') '-' == "a-b-c"
test "words and lines" := "two  words".words == ["two", "words"] ∧ "a\nb\n".lines == ["a", "b"]
test "numbers" := "42".toNat == Some 42 ∧ "-7".toInt == Some (-7)
test "toNat does not trim" := " 42 ".toNat == None ∧ " 42 ".trim.toNat == Some 42
test "trim and slices" := "  tea ".trim == "tea" ∧ "teapot".take 3 == "tea"
test "prefixes" := "L68".stripPrefix "L" == Some "68"
test "length counts characters" := "héllo".length == 5
-- end text

-- begin map
def wordCounts (words: List Text): Map Text Nat :=
  words.foldLeft Map.empty (counts word => counts.insertWith word 1 (a b => a + b))

test "counts" := (wordCounts ["a", "b", "a"]).get "a" == Some 2
test "missing key" := (wordCounts ["a"]).get "z" == None
test "in key order" := (wordCounts ["b", "a", "b"]).toList == [("a", 1), ("b", 2)]
test "group by" :=
  (["tea", "milk", "pot"].groupBy (word => word.length)).get 3 |> .map (group => group.toList) == Some ["tea", "pot"]
test "from pairs" := [(2, "b"), (1, "a")].toMap == Map.fromList [(1, "a"), (2, "b")]
test "equal however built" := Map.fromList [(1, "a"), (2, "b")] == Map.fromList [(2, "b"), (1, "a")]
-- end map

-- begin set
def seen: Set Nat := [3, 1, 3, 2].toSet
def sets: List (Set Nat) := [[1, 2].toSet, [2, 3].toSet]

test "duplicates go" := seen.size == 3 ∧ seen.toList == [1, 2, 3]
test "membership" := seen.contains 2 ∧ ¬(seen.contains 5)
test "set algebra" := Set.union seen [9].toSet == [1, 2, 3, 9].toSet
test "union a list of sets" := sets.unionAll == [1, 2, 3].toSet
-- end set

-- begin nonempty
def groupAnswers: NonEmptyList (Set Char) := [['a', 'b', 'c'].toSet, ['b', 'c'].toSet, ['c', 'd'].toSet]
def numbers: NonEmptyList Nat := [3, 9, 4]

def describe: NonEmptyList Nat → Text
  | [only] => "just ${only}"
  | [first, ..rest] => "${first} and ${rest.length} more"

test "no Option" := groupAnswers.intersectAll == ['c'].toSet
test "reduce and maximum" := numbers.maximum == 9 ∧ numbers.reduce Nat.add == 16
test "map keeps it non-empty" := (numbers.map (n => n * 10)).head == 30
test "no [] arm" := describe [7] == "just 7" ∧ describe numbers == "3 and 2 more"
test "from a list" := [4, 5, 6].toNonEmpty.maximum == 6 ∧ ([]: List Nat).nonEmpty == None
-- end nonempty

-- begin vec
def row: Vec Nat 3 := VCons 4 (VCons 5 (VCons 6 VNil))

test "a Vec knows its length" := row.toList == [4, 5, 6]
test "head needs no Option" := row.head == 4
test "zipWith needs equal lengths" := (Vec.zipWith row row (a b => a + b)).toList == [8, 10, 12]
-- end vec

-- begin array
def tally (digits: List Nat): Array Nat :=
  digits.foldLeft (Array.replicate (count := 10) 0) (counts digit => counts.modify digit (n => n + 1))

test "an array of counts" := (tally [3, 1, 3, 3]).toList == [0, 1, 0, 3, 0, 0, 0, 0, 0, 0]
test "get gives an Option" := (tally [3]).get 3 == Some 1 ∧ (tally [3]).get 10 == None
test "getOr gives a fallback" := (tally [3]).getOr 12 0 == 0
test "set out of range changes nothing" := ([5, 6].toArray).set 2 9 == [5, 6].toArray

test "getLt needs no Option when the index is in range" := ([7, 8, 9].toArray).getLt 1 == 8
-- end array
