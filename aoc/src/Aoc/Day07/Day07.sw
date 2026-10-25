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
-- splitter added up (`splitRow`). Both work on whole rows of `width`
-- columns: a row shifted one place right (`shiftRight`) puts each column's
-- left neighbour in it, shifted left (`shiftLeft`) its right one, and
-- `around` sees both.
--
-- Both answers are proved right for every manifold in `Aoc.Day07.Proofs`
-- (Spec/Spec.sw states the puzzle over the manifold, with the timelines
-- as explicit lists of the splitters they pass; Proofs/Part1.sw and
-- Proofs/Part2.sw), and the
-- tests are in `Aoc.Day07.Tests` (Tests/); `run` checks neither.

namespace Aoc.Day07
import Std (Abort, Fail, Fin, IO, List, Nat, Option, Result, Text, Vec)
import Std.Abort (toOption)

def main(): {IO, Fail} () :=
  let manifold := (checkManifold IO.readAllLines()).orFail
  IO.print "Part 1: ${solvePart1 manifold}"
  IO.print "Part 2: ${solvePart2 manifold}"

-- The rows below S, each a flag per column (True for a splitter), all
-- `width` long; S is in column `start` of the row above the first.
type Manifold = { width: Nat, start: Fin width, rows: List (Vec Bool width) }

-- `None` if there is no S. (S is always inside the grid, as wide as the
-- widest line; `Fin.ofNatCheck` checks it.)
def parseManifoldOption (lines: List Text): Option Manifold := toOption (() => parseManifold lines)

-- The strict parser `main` uses. `parseManifoldOption` is forgiving (any character
-- but ^ is empty space); `checkManifold` refuses a manifold with a character
-- other than . ^ S (naming its line and column, counting from 1), or with no
-- S, and otherwise gives exactly `parseManifoldOption lines`
-- (`Aoc.Day07.Proofs.checkManifoldParses`), so the proofs about the parser
-- describe what is printed. An S may be anywhere; the first is the start.
def checkManifold (lines: List Text): Result Manifold Text :=
  match manifoldError lines with
    | Some message => Err message
    | None =>
      match parseManifoldOption lines with
        | Some manifold => Ok manifold
        | None => Err "expected a line with an S, got none"

-- The first character that isn't . ^ or S, if any.
def manifoldError (lines: List Text): Option Text :=
  lines.withIndex.findMap (((lineIndex, line)) =>
    line.toList.withIndex.findMap (((columnIndex, ch)) =>
      if ch == '.' ∨ ch == '^' ∨ ch == 'S' then None
      else Some "line ${lineIndex + 1}, column ${columnIndex + 1}: expected . or ^ or S, got '${ch}'"))

-- Each step that finds nothing gives up, which makes the result `None`.
def parseManifold (lines: List Text): {Abort} Manifold :=
  let width := gridWidth lines
  let (rowIndex, columnIndex) := (findStart lines).orAbort
  let start := (Fin.ofNatCheck width columnIndex).orAbort
  { width, start, rows = (lines.drop (rowIndex + 1)).map (splitterRow width) }

-- Row and column of the first S, reading top to bottom, left to right.
def findStart (lines: List Text): Option (Nat, Nat) :=
  lines.withIndex.findMap (((rowIndex, line)) => (line.toList.findIndex (== 'S')).map (columnIndex => (rowIndex, columnIndex)))

-- The widest line's length.
def gridWidth (lines: List Text): Nat := lines.foldLeft 0 widen

def widen (width: Nat) (line: Text): Nat := Nat.max width line.length

-- A line's splitter flags, `width` of them: past the end of the line there
-- is empty space.
def splitterRow (width: Nat) (line: Text): Vec Bool width := flagsOf width line.toList

def flagsOf: (width: Nat) → List Char → Vec Bool width
  | Zero, _ => VNil
  | Succ remaining, Nil => VCons False (flagsOf remaining Nil)
  | Succ remaining, Cons ch rest => VCons (isSplitter ch) (flagsOf remaining rest)

def isSplitter (ch: Char): Bool := ch == '^'

-- Part 1: carry the beams down, a flag per column, adding up the splitters
-- each row's beams reach.
def solvePart1 (manifold: Manifold): Nat :=
  splitsBelow (Vec.tabulate manifold.width (== manifold.start)) manifold.rows

-- `beams` are the beams falling into the first of `rows`.
def splitsBelow (beams: Vec Bool w): List (Vec Bool w) → Nat
  | Nil => 0
  | Cons row rest => splitsIn row beams + splitsBelow (fall row beams) rest

-- The splitters of a row that beams reach.
def splitsIn (row: Vec Bool w) (beams: Vec Bool w): Nat := (Vec.zipWith row beams (∧)).count (hit => hit)

-- The beams falling out of a row: a beam passes a column with no splitter,
-- and a splitter with a beam on it sends one down each side.
def fall (row: Vec Bool w) (beams: Vec Bool w): Vec Bool w :=
  let hit := Vec.zipWith row beams (∧)
  Vec.zipWith3 (Vec.zipWith row beams (splitter beam => beam ∧ not splitter))
    (hit.shiftRight False) (hit.shiftLeft False) (pass left right => pass ∨ (left ∨ right))

-- Part 2: the timelines of a particle starting at S.
def solvePart2 (manifold: Manifold): Nat := (timelineCounts manifold).get manifold.start

-- For each column, the timelines of a particle falling into it from the row
-- of S.
def timelineCounts (manifold: Manifold): Vec Nat manifold.width :=
  manifold.rows.foldRight (Vec.replicate manifold.width 1) splitRow

-- A row's timeline counts, given the counts of the row below it: a column
-- with no splitter has the count of the column below, and a splitter the
-- counts of the columns below on both sides added up.
def splitRow (row: Vec Bool w) (below: Vec Nat w): Vec Nat w :=
  -- The pad 1: past either edge a particle has left the manifold, and that
  -- is one completed timeline.
  let sides := below.around 1 (left _ right => left + right)
  Vec.zipWith3 row below sides (splitter here sides => if splitter then sides else here)
