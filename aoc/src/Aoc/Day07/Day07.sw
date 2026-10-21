-- Advent of Code 2025, day 7: a tachyon beam falls through a manifold of
-- splitters (^). It enters at S and moves down; a splitter stops it and
-- sends a new beam down from the cell on each side of it. Beams that meet
-- merge. Part 1 counts the splitters a beam reaches (the times it is split).
-- Part 2 follows a single particle that takes both ways at every splitter,
-- each in its own timeline, and counts the timelines.
--
--   $ cd aoc && stitchwort run Aoc.Day07.main < inputs/day07.txt
--
-- The puzzle input is committed in aoc/inputs/ (D119).
--
-- The rows below S become rows of splitter flags, all as wide as the widest
-- line. Part 1 carries the beams down row by row, a flag per column
-- (`fall`). Part 2 works up from the bottom: below the last row a particle
-- in any column has one timeline left, and a column of a row above has the
-- timelines of the column it falls into, or of both columns beside its
-- splitter added up (`splitRow`). Both are one pass over a row per row.
--
-- Both answers are proved right for every input in `Aoc.Day07.Proofs`
-- (Proofs/Spec.sw states the puzzle with the timelines as explicit lists of
-- the splitters they pass; Proofs/Correct.sw), which `run` does not check.

namespace Aoc.Day07

def main(): {IO} () :=
  match parseManifold (IO.readAllLines()) with
    | Nothing       => IO.print "There is no S."
    | Just manifold =>
      IO.print "Part 1: ${solvePart1 manifold}"
      IO.print "Part 2: ${solvePart2 manifold}"

-- The rows below S, each a flag per column (True for a splitter), all
-- `width` long; S is in column `start` of the row above the first.
type Manifold = { width: Nat, start: Nat, rows: List (List Bool) }

def example: List Text :=
  [ ".......S.......", "...............", ".......^.......", "...............",
    "......^.^......", "...............", ".....^.^.^.....", "...............",
    "....^.^...^....", "...............", "...^.^...^.^...", "...............",
    "..^...^.....^..", "...............", ".^.^.^.^.^...^.", "..............." ]

-- `Nothing` if there is no S.
def parseManifold (lines: List Text): Maybe Manifold :=
  let width := gridWidth lines
  (findStart lines).map (((r, c)) =>
    ({ width, start = c, rows = (lines.drop (r + 1)).map (splitterRow width) }: Manifold))

-- Row and column of the first S, reading top to bottom, left to right.
def findStart (lines: List Text): Maybe (Nat, Nat) := startFrom 0 lines

-- `r` is the row number of the first of `lines`.
def startFrom (r: Nat): List Text -> Maybe (Nat, Nat)
  | Nil            => Nothing
  | Cons line rest =>
    match columnOf 'S' line.toList with
      | Just c  => Just (r, c)
      | Nothing => startFrom (r + 1) rest

-- Where `ch` first appears.
def columnOf (ch: Char): List Char -> Maybe Nat
  | Nil       => Nothing
  | Cons x xs => if x == ch then Just 0 else (columnOf ch xs).map Succ

test "find start" := (findStart example, findStart ["..", ".S", "S."], findStart [".."]) == (Just (0, 7), Just (1, 1), Nothing)

-- The widest line's length.
def gridWidth (lines: List Text): Nat := lines.foldLeft widen 0

def widen (width: Nat) (line: Text): Nat := Nat.max width line.length

-- A line's splitter flags, padded to `width` columns.
def splitterRow (width: Nat) (line: Text): List Bool := (line.toList.map isSplitter).padRight width False

def isSplitter (ch: Char): Bool := ch == '^'

test "splitter row" := splitterRow 5 ".^." == [False, True, False, False, False]

-- Part 1: carry the beams down, a flag per column, adding up the splitters
-- each row's beams reach.
def solvePart1 (manifold: Manifold): Nat :=
  splitsBelow ((List.range manifold.width).map (c => c == manifold.start)) manifold.rows

-- `beams` are the beams falling into the first of `rows`.
def splitsBelow (beams: List Bool): List (List Bool) -> Nat
  | Nil            => 0
  | Cons row rest  => splitsIn row beams + splitsBelow (fall False row beams) rest

-- The splitters of a row that beams reach.
def splitsIn (row: List Bool) (beams: List Bool): Nat := (List.zipWith (s b => s && b) row beams).count (x => x)

-- The beams falling out of a row: a beam passes a column with no splitter,
-- and a splitter with a beam on it sends one down each side. `fromLeft`
-- says whether the column left of the first sends a beam into it.
def fall (fromLeft: Bool): List Bool -> List Bool -> List Bool
  | Cons s ss, Cons b bs => Cons ((b && not s) || fromLeft || (ss.headOr False && bs.headOr False)) (fall (s && b) ss bs)
  | _,         _         => Nil

test "fall" := fall False [False, True, False, False] [True, True, False, False] == [True, False, True, False]

-- Part 2: the timelines of a particle starting at S.
def solvePart2 (manifold: Manifold): Nat := (timelineCounts manifold).getOr 1 manifold.start

-- For each column, the timelines of a particle falling into it from the row
-- of S.
def timelineCounts (manifold: Manifold): List Nat :=
  manifold.rows.foldRight (row below => splitRow 1 row below) (List.replicate manifold.width 1)

-- A row's timeline counts, given the counts of the row below it: a column
-- with no splitter has the count of the column below, and a splitter the
-- counts of the columns below on both sides added up. Past either edge a
-- particle has left the manifold: one timeline. `left` is the count of the
-- column left of the first, below.
def splitRow (left: Nat): List Bool -> List Nat -> List Nat
  | Cons s ss, Cons here rest => Cons (if s then left + rest.headOr 1 else here) (splitRow here ss rest)
  | _,         _              => Nil

test "split row" := splitRow 1 [False, True, False, True] [2, 3, 4, 5] == [2, 6, 4, 5]

test "example part 1" := Maybe.map solvePart1 (parseManifold example) == Just 21
test "example part 2" := Maybe.map solvePart2 (parseManifold example) == Just 40
test "splitter at the left edge" := Maybe.map (m => (solvePart1 m, solvePart2 m)) (parseManifold ["S.", "^.", ".."]) == Just (1, 2)
test "splitter at the right edge" := Maybe.map (m => (solvePart1 m, solvePart2 m)) (parseManifold [".S", ".^", ".^"]) == Just (1, 2)
test "beams merge" := Maybe.map (m => (solvePart1 m, solvePart2 m)) (parseManifold ["..S..", "..^..", ".^.^.", "..^.."]) == Just (4, 6)
test "nothing below S" := Maybe.map (m => (solvePart1 m, solvePart2 m)) (parseManifold ["^^", ".S"]) == Just (0, 1)
test "no S" := Maybe.map solvePart1 (parseManifold ["..^.."]) == Nothing
