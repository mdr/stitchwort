-- Day 7's tests: the example from the puzzle and unit tests. Kept apart from
-- the program, so `stitchwort run Aoc.Day07.main` doesn't check them.

namespace Aoc.Day07.Tests
import Aoc.Day07 (..)
import Std (Bool, Fail, IO, List, Option, Pair, Result, Text, Vec)

def example: List Text := """
  .......S.......
  ...............
  .......^.......
  ...............
  ......^.^......
  ...............
  .....^.^.^.....
  ...............
  ....^.^...^....
  ...............
  ...^.^...^.^...
  ...............
  ..^...^.....^..
  ...............
  .^.^.^.^.^...^.
  ...............
  """.lines

def row4 (a: x) (b: x) (c: x) (d: x): Vec x 4 := VCons a (VCons b (VCons c (VCons d VNil)))

test "find start" := (findStart example, findStart ["..", ".S", "S."], findStart [".."]) == (Some (0, 7), Some (1, 1), None)
test "manifold" := Option.map (parseManifoldOption example) (m => (m.width, m.start.toNat, m.rows.length)) == Some (15, 7, 15)
test "splitter row" := ((splitterRow 5 ".^.").toList, (splitterRow 2 ".^.").toList) == ([False, True, False, False, False], [False, True])
test "fall" := (fall (row4 False True False False) (row4 True True False False)).toList == [True, False, True, False]
test "split row" := (splitRow (row4 False True False True) (row4 2 3 4 5)).toList == [2, 6, 4, 5]
test "example part 1" := Option.map (parseManifoldOption example) solvePart1 == Some 21
test "example part 2" := Option.map (parseManifoldOption example) solvePart2 == Some 40
test "splitter at the left edge" := Option.map (parseManifoldOption ["S.", "^.", ".."]) (m => (solvePart1 m, solvePart2 m)) == Some (1, 2)
test "splitter at the right edge" := Option.map (parseManifoldOption [".S", ".^", ".^"]) (m => (solvePart1 m, solvePart2 m)) == Some (1, 2)
test "beams merge" := Option.map (parseManifoldOption ["..S..", "..^..", ".^.^.", "..^.."]) (m => (solvePart1 m, solvePart2 m)) == Some (4, 6)
test "nothing below S" := Option.map (parseManifoldOption ["^^", ".S"]) (m => (solvePart1 m, solvePart2 m)) == Some (0, 1)
test "no S" := Option.map (parseManifoldOption ["..^.."]) solvePart1 == None

-- What `main` prints and how it ends, for some input lines.
def ran (lines: List Text): Pair (List Text) (Result Bool Text) :=
  IO.simulate lines (() => Result.map (Fail.toResult main) (u => True))

test "main with no S" := ran ["..^.."] == MkPair [] (Err "expected a line with an S, got none")
test "main with a final blank line" := ran ["..S..", "..^..", ""] == MkPair ["Part 1: 1", "Part 2: 2"] (Ok True)

-- The strict parser: what it rejects, and what it still accepts.
test "an unknown character" := ran ["..S..", "..x.."] == MkPair [] (Err "line 2, column 3: expected . or ^ or S, got 'x'")
test "the first unknown character wins" := ran ["..S?", "a"] == MkPair [] (Err "line 1, column 4: expected . or ^ or S, got '?'")
test "a space is not empty space" := ran ["S.", ". "] == MkPair [] (Err "line 2, column 2: expected . or ^ or S, got ' '")
test "a lower-case s" := ran ["..s.."] == MkPair [] (Err "line 1, column 3: expected . or ^ or S, got 's'")
test "an unknown character beats a missing S" := ran ["..x.."] == MkPair [] (Err "line 1, column 3: expected . or ^ or S, got 'x'")
test "check with no S" := Result.map (checkManifold ["...."]) (m => m.width) == Err "expected a line with an S, got none"
test "the manifold is what the parser reads" :=
  Result.map (checkManifold example) (m => (m.width, m.start.toNat, m.rows.length)) == Ok (15, 7, 15)
test "one column, both branches leave" := ran ["S", "^", "."] == MkPair ["Part 1: 1", "Part 2: 2"] (Ok True)
test "a short intermediate row is padded" := ran ["..S..", "..^..", ".", ".^.^."] == MkPair ["Part 1: 3", "Part 2: 4"] (Ok True)
test "S below another S" := ran ["S", ".S", "^"] == MkPair ["Part 1: 1", "Part 2: 2"] (Ok True)
