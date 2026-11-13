--| Advent of Code 2021, day 13: dots on a sheet of transparent paper, one
--| `x,y` per line (x across, y down), a blank line, then instructions to
--| fold the sheet, `fold along y=7` or `fold along x=5`. Folding along a
--| line reflects every dot beyond it onto the near half; dots that land on
--| each other become one. Part 1 counts the dots after the first fold. Part
--| 2 folds the sheet every time; the dots then spell eight capital letters,
--| and the answer is the picture they make.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day13.main < inputs/2021/day13.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program keeps the dots as a list without repeats: each fold moves
--| every dot to where it lands and drops the repeats. The parser checks
--| what the puzzle promises: no dot is on a fold line when that fold is
--| made, and no dot is further beyond a line than the sheet reaches on the
--| near side. The proofs that the answers are the puzzle's are in
--| `Aoc.Year2021.Day13.Proofs` (Proofs/), the tests in
--| `Aoc.Year2021.Day13.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day13
import Aoc.Common (Point)
import Std (Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, lines, nat, pick, section, text)

def main(): {IO, Fail} () :=
  let paper := parsePaper IO.readAll()
  IO.print "Part 1: ${solvePart1 paper}"
  IO.print "Part 2:\n${showPicture (solvePart2 paper)}"

--| A fold along the vertical line `x = line` (the right half folds over to
--| the left) or along the horizontal line `y = line` (the bottom half folds
--| up).
type Fold =
  | AlongX (line: Nat)
  | AlongY (line: Nat)

--| The dots, then the folds, in order. A dot is a point: `x` across from
--| the left edge, `y` down from the top.
type Paper = { dots: List Point, folds: List Fold }

--| The input: the dots, one per line, a blank line, and the folds, one per
--| line. Fails if a fold has a dot on its line, or a dot further beyond it
--| than the sheet reaches on the near side.
def parsePaper (input: Text): {Fail} Paper := checkPaper (Parse.all input readPaper)

def readPaper(): {Parse} Paper :=
  let dots := section readDot |> .toList
  let folds := lines readFold |> .toList
  { dots, folds }

def readDot(): {Parse} Point :=
  let x := nat()
  char ','
  let y := nat()
  { x, y }

def readFold(): {Parse} Fold :=
  text "fold along "
  let along := pick [("x=", AlongX), ("y=", AlongY)]
  along nat()

--| The paper, if every fold can be made as the puzzle promises; otherwise
--| fail, naming the first fold that can't and a dot in its way.
def checkPaper (paper: Paper): {Fail} Paper := match firstBlocked paper.dots paper.folds with
  | Some (index, dot) => Fail.fail "fold ${index + 1}: the dot at ${dot.x},${dot.y} is on its line, or further beyond it than the sheet reaches on the near side"
  | None => paper

--| The first fold that has a dot (after the folds before it) on its line
--| or too far beyond it, with its index and that dot.
def firstBlocked (dots: List Point) (folds: List Fold): Option (Nat, Point) := firstBlockedFrom 0 dots folds

def firstBlockedFrom (index: Nat) (dots: List Point): List Fold → Option (Nat, Point)
  | [] => None
  | [fold, ..rest] =>
    match dots.find (dot => not (clears fold dot)) with
      | Some dot => Some (index, dot)
      | None => firstBlockedFrom (index + 1) (foldOnce dots fold) rest

--| A dot is clear of a fold when it isn't on the line and isn't further
--| beyond it than the line is from the near edge (so its reflection is on
--| the sheet).
def clears (fold: Fold) (dot: Point): Bool := match fold with
  | AlongX line => dot.x != line && dot.x <= 2 * line
  | AlongY line => dot.y != line && dot.y <= 2 * line

--| Where a dot ends up after a fold: reflected across the line if it is
--| beyond it, where it was otherwise.
def foldDot (fold: Fold) (dot: Point): Point := match fold with
  | AlongX line => if line < dot.x then { dot | x = 2 * line - dot.x } else dot
  | AlongY line => if line < dot.y then { dot | y = 2 * line - dot.y } else dot

--| One fold: every dot moves to where it lands, and dots that land
--| together become one.
def foldOnce (dots: List Point) (fold: Fold): List Point := dots.map (foldDot fold) |> .unique

--| The dots after the folds, in order, each once.
def foldAll (folds: List Fold) (dots: List Point): List Point := folds.foldLeft dots.unique foldOnce

--| Part 1: how many dots are left after the first fold.
def solvePart1 (paper: Paper): Nat := (foldAll (paper.folds.take 1) paper.dots).length

--| Part 2: the picture after every fold.
def solvePart2 (paper: Paper): List (List Char) := render (foldAll paper.folds paper.dots)

--| The dots as rows of `#` (a dot) and `.` (none), from the top left corner
--| to the rightmost and lowest dot.
def render (dots: List Point): List (List Char) :=
  List.range 0 (height dots) |> .map (y => List.range 0 (width dots) |> .map (x => if dots.any (== { x, y }) then '#' else '.'))

--| How many columns and rows the dots need.
def width (dots: List Point): Nat := dots.foldRight 0 (dot widest => Nat.max (dot.x + 1) widest)

def height (dots: List Point): Nat := dots.foldRight 0 (dot lowest => Nat.max (dot.y + 1) lowest)

def showPicture (picture: List (List Char)): Text := picture.map Text.fromList |> Text.joinWith "\n"
