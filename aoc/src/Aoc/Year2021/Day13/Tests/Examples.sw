--| Day 13's tests: the puzzle's example, the parser, and a reader for
--| the letters part 2's picture spells.
-- Kept apart from the program, so
-- `stitchwort run Aoc.Year2021.Day13.main` doesn't check them.

namespace Aoc.Year2021.Day13.Tests
import Aoc.Year2021.Day13 (..)
import Std (Fail, List, Option, Text)
import Aoc.Year2021.Day13.Spec (cellAt)

def parsed (input: Text): Result Paper Text := Fail.toResult (() => parsePaper input)

def paperOf (input: Text): Paper := Fail.orElse { dots = [], folds = [] } (() => parsePaper input)

def exampleInput: Text := """
  6,10
  0,14
  9,10
  0,3
  10,4
  4,11
  6,0
  6,12
  4,1
  0,13
  10,12
  3,4
  3,0
  8,4
  1,10
  2,14
  8,10
  9,0

  fold along y=7
  fold along x=5
  """

def example: Paper := paperOf exampleInput

--| The hypotheses of `cellSomeInside` and `rowWidth` can hold.
-- (the audit's random inputs never met them)
theorem oneDotShown: cellAt (render [{ x = 0, y = 0 }]) { x = 0, y = 0 } = Some '#' := rfl

theorem oneDotRow: ['#'] ∈ render [{ x = 0, y = 0 }] := Inl rfl

--| The hypothesis of the parser's theorems can hold.
-- (the audit's random texts never parse)
theorem smallParses: Fail.toResult (() => parsePaper """
  1,2
  3,0

  fold along y=1
  """) = Ok { dots = [{ x = 1, y = 2 }, { x = 3, y = 0 }], folds = [AlongY 1] } := rfl

test "parse the example" := example.dots.length == 18 && example.folds == [AlongY 7, AlongX 5]
test "example, part 1" := solvePart1 example == 17
test "example, after both folds: a square" := showPicture (solvePart2 example) == "#####\n#...#\n#...#\n#...#\n#####"
test "example, the first fold's picture" :=
  showPicture (render (foldAll [AlongY 7] example.dots))
    == "#.##..#..#.\n#...#......\n......#...#\n#...#......\n.#.#..#.###"

test "a dot on a fold line" := parsed """
  1,2
  3,1

  fold along y=1
  """ == Err "fold 1: the dot at 3,1 is on its line, or further beyond it than the sheet reaches on the near side"
test "a dot too far beyond a fold line" := parsed """
  1,0
  7,1

  fold along x=3
  """ == Err "fold 1: the dot at 7,1 is on its line, or further beyond it than the sheet reaches on the near side"
test "a dot on the second fold's line once the first is made" := parsed """
  0,0
  2,4

  fold along y=2
  fold along x=2
  """ == Err "fold 2: the dot at 2,0 is on its line, or further beyond it than the sheet reaches on the near side"
test "a bad fold" := parsed "1,2\n\nfold along z=1\n" == Err "line 3, column 12: expected 'x=' or 'y=', got 'z='"
test "no blank line" :=
  parsed "1,2\nfold along y=1\n" == Err "line 2, column 1: expected a number or a blank line, got 'f'"
test "a dot listed twice is one dot" := solvePart1 (paperOf """
  1,0
  1,0
  1,2

  fold along y=1
  """) == 1
test "no folds: the dots as listed, each once" :=
  solvePart1 { dots = [{ x = 1, y = 0 }, { x = 1, y = 0 }, { x = 0, y = 2 }], folds = [] } == 2

--| A reader for the capital letters part 2's picture spells, each 4
--| columns wide with a column of space after it, in the puzzle's font. Not
--| proved: the proofs are about the picture.
def glyphs: List (Text, Char) := [
  (".##.#..##...#...#..#.##.", 'C'),
  ("..##...#...#...##..#.##.", 'J'),
  ("#..##..######..##..##..#", 'H'),
  (".##.#..##..######..##..#", 'A'),
  ("####...#..#..#..#...####", 'Z'),
  ("#..##.#.##..#.#.#.#.#..#", 'K'),
  ("#..##..##..##..##..#.##.", 'U'),
  ("###.#..####.#..##..####.", 'B'),
  ("#####...###.#...#...####", 'E'),
  ("#####...###.#...#...#...", 'F'),
  (".##.#..##...#.###..#.###", 'G'),
  ("#...#...#...#...#...####", 'L'),
  ("###.#..##..####.#...#...", 'P'),
  ("###.#..##..####.#.#.#..#", 'R')
]

def readLetters (picture: List (List Char)): Text :=
  let width := picture.headOr [] |> .length
  List.range 0 ((width + 1) / 5)
    |> .map (i =>
      let glyph := picture.flatMap (row => (row.drop (5 * i)).take 4) |> Text.fromList
      glyphs.lookup glyph |> .getOrElse '?')
    |> Text.fromList

test "the example's square isn't a letter" := readLetters (solvePart2 example) == "?"
