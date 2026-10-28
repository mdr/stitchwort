-- Day 4's tests: the examples from the puzzle and unit tests. Kept apart
-- from the program, so `stitchwort run Aoc.Year2024.Day04.main` doesn't check
-- them. A `.` is a letter like any other, as in the puzzle's diagrams.

namespace Aoc.Year2024.Day04.Tests
import Aoc.Year2024.Day04 (..)
import Std (List, Text)

def example: Grid := parseGrid """
  MMMSXXMASM
  MSAMXMSMSA
  AMXSXMAAMM
  MSAMASMSMX
  XMASAMXAMM
  XXAMMXXAMA
  SMSMSASXSS
  SAXAMASAAA
  MAMMMXMMMM
  MXMXAXMASX
  """.lines

-- The example with the letters of no XMAS replaced by `.`.
def exampleXmasOnly: Grid := parseGrid """
  ....XXMAS.
  .SAMXMS...
  ...S..A...
  ..A.A.MS.X
  XMASAMX.MM
  X.....XA.A
  S.S.S.S.SS
  .A.A.A.A.A
  ..M.M.M.MM
  .X.X.XMASX
  """.lines

-- The example with the letters of no X-MAS replaced by `.`.
def exampleCrossesOnly: Grid := parseGrid """
  .M.S......
  ..A..MSMS.
  .M.S.MAA..
  ..A.ASMSM.
  .M.S.M....
  ..........
  S.S.S.S.S.
  .A.A.A.A..
  M.M.M.M.M.
  ..........
  """.lines

def part1 (lines: List Text): Nat := solvePart1 (parseGrid lines)

def part2 (lines: List Text): Nat := solvePart2 (parseGrid lines)

test "example, part 1" := solvePart1 example == 18
test "example, part 2" := solvePart2 example == 9
test "example with only the XMAS letters, part 1" := solvePart1 exampleXmasOnly == 18
test "example with only the X-MAS letters, part 2" := solvePart2 exampleCrossesOnly == 9
test "the puzzle's small diagram" := part1 ["..X...", ".SAMX.", ".A..A.", "XMAS.S", ".X...."] == 4
test "parse" := parseGrid ["XM", "AS"] == { rows = [['X', 'M'], ['A', 'S']] }
test "no lines" := part1 [] == 0 ∧ part2 [] == 0
test "across" := part1 ["XMAS"] == 1
test "across, backwards" := part1 ["SAMX"] == 1
test "both ways, overlapping" := part1 ["XMASAMX"] == 2
test "down and up" := part1 ["XS", "MA", "AM", "SX"] == 2
test "down to the right" := part1 ["X...", ".M..", "..A.", "...S"] == 1
test "down to the left" := part1 ["...X", "..M.", ".A..", "S..."] == 1
test "up to the left" := part1 ["S...", ".A..", "..M.", "...X"] == 1
test "up to the right" := part1 ["...S", "..A.", ".M..", "X..."] == 1
test "eight from one X" := part1 ["S..S..S", ".A.A.A.", "..MMM..", "SAMXMAS", "..MMM..", ".A.A.A.", "S..S..S"] == 8
test "too short" := part1 ["XMA", "M", "A"] == 0
test "rows of different lengths" := part1 ["X", "MM", "AAA", "SSSS"] == 2
test "a gap in a short row" := part1 ["X...", "M", "A...", "S..."] == 1 ∧ part1 ["X...", "", "A...", "S..."] == 0
test "a cross" := part2 ["M.S", ".A.", "M.S"] == 1
test "a cross, every way round" :=
  part2 ["M.M", ".A.", "S.S"] == 1 ∧ part2 ["S.S", ".A.", "M.M"] == 1 ∧ part2 ["S.M", ".A.", "S.M"] == 1
test "MAM is not a cross" := part2 ["M.M", ".A.", "M.M"] == 0
test "a plus is not a cross" := part2 [".M.", "MAS", ".S."] == 0
test "two crosses sharing letters" := part2 ["M.S.M", ".A.A.", "M.S.M"] == 2
test "the centre must be an A" := part2 ["M.S", ".X.", "M.S"] == 0
test "a cross in rows of different lengths" := part2 ["M.S", ".A", "M.S"] == 1 ∧ part2 ["M.S", ".A", "M."] == 0
