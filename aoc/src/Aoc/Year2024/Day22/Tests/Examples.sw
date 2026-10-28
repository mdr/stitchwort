-- Day 22's tests: the examples from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day22.main` doesn't
-- check them. Answers not in the puzzle were cross-checked with a separate
-- Python solver.

namespace Aoc.Year2024.Day22.Tests
import Aoc.Year2024.Day22 (..)
import Aoc.Year2024.Day22.Spec (bananas, evolve, mix, mostBananas, prune, sellingPrice)
import Std (Fail, Int, List, Map, Nat, Option, Result, Text)

def parsed (input: Text): Result (List Nat) Text := Fail.toResult (() => parseBuyers input)

def changesOf (first: Int) (second: Int) (third: Int) (fourth: Int): Changes := { first, second, third, fourth }

-- The puzzle's sequence for part 2's example.
def best: Changes := changesOf (-2) 1 (-1) 3

-- Secrets.
test "mixing 15 into 42 gives 37" := mix 15 42 == 37
test "pruning 100000000 gives 16113920" := prune 100000000 == 16113920
test "the ten secrets after 123" :=
  secrets 10 123 == [123, 15887950, 16495136, 527345, 704524, 1553684, 12683156, 11100544, 12249484, 7753432, 5908254]
test "the 2000th secrets" := [1, 10, 100, 2024].map (buyer => Nat.iterate 2000 nextSecret buyer) == [8685429, 4700978, 15273692, 8667524]
test "the step is the puzzle's, for secrets of 24 bits and more" :=
  [0, 1, 123, 16777215, 16777216, 100000000, 123456789012].all (secret => nextSecret secret == evolve secret)
test "0 stays 0" := nextSecret 0 == 0

-- Part 1.
test "part 1 example" := (parsed "1\n10\n100\n2024\n" |> .map solvePart1) == Ok 37327623
test "part 1 with no buyers" := solvePart1 [] == 0

-- Part 2.
test "the first ten prices of 123" := prices 9 123 == [3, 0, 6, 5, 4, 4, 6, 4, 4, 2]
test "-1,-1,0,2 sells at 6 for 123" := (firstSales (prices 9 123)).get (changesOf (-1) (-1) 0 2) == Some 6
test "a sale needs four changes" := (firstSales (prices 3 123)).size == 0 && (firstSales (prices 4 123)).size == 1
test "the example sequence's sales" := [1, 2, 3, 2024].map (buyer => (firstSales (prices 2000 buyer)).get best) == [Some 7, Some 7, None, Some 9]
test "part 2 example" := (parsed "1\n2\n3\n2024\n" |> .map solvePart2) == Ok 23
test "its best sequence" := (bananasBySequence 2000 [1, 2, 3, 2024]).getOr best 0 == 23
test "part 2 on part 1's example" := solvePart2 [1, 10, 100, 2024] == 24
test "part 2 with no buyers" := solvePart2 [] == 0
test "a buyer whose prices never change" := bestTotal 2000 [0] == 0 && (firstSales (prices 2000 0)).toList == [(changesOf 0 0 0 0, 0)]
test "the first occurrence, not the best" := (firstSales [5, 4, 3, 2, 1, 9, 4, 3, 2, 1, 0]).get (changesOf (-1) (-1) (-1) (-1)) == Some 1

-- The program against the spec, on few secrets.
test "totals are the spec's bananas" :=
  let buyers := [1, 2, 3, 2024]
  (bananasBySequence 50 buyers).keys |> .all (sequence => (bananasBySequence 50 buyers).getOr sequence 0 == bananas 50 buyers sequence)
test "sequences no buyer shows earn nothing" := [best, changesOf 9 9 9 9, changesOf 0 0 0 0].all (sequence => bananas 50 [1, 2, 3, 2024] sequence == 0)
test "the spec's first sale" := sellingPrice best [5, 3, 4, 3, 6, 1, 2, 1, 2, 5] == Some 6
test "the most over the shown sequences" :=
  let buyers := [1, 2, 3, 2024]
  bestTotal 50 buyers == mostBananas (bananasBySequence 50 buyers).keys 50 buyers

-- Parsing.
test "parse" := parsed "1\n10\n100\n2024\n" == Ok [1, 10, 100, 2024]
test "parse without a final line break" := parsed "1\n2" == Ok [1, 2]
test "a line that isn't a number" := parsed "1\nx\n" == Err "line 2, column 1: expected a number, got 'x'"
test "an empty input has no buyers" := parsed "" == Ok []
