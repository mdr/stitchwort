--| Advent of Code 2021, day 5: lines of hydrothermal vents on the ocean
--| floor. Each line of the input is a line segment, `x1,y1 -> x2,y2`, from
--| one grid point to another, and covers the grid points on it, both ends
--| included. Every line is horizontal, vertical or diagonal at exactly 45
--| degrees. Part 1 takes only the horizontal and vertical lines and counts
--| the points where at least two of them overlap; part 2 counts the same
--| with every line.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day05.main < inputs/2021/day05.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program lists the points each line covers, counts how often each
--| point is listed (`Map.counts`), and counts the points listed at least
--| twice. The proofs that both answers are the number of points where at
--| least two lines overlap, for every input, are in
--| `Aoc.Year2021.Day05.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2021.Day05.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day05
import Std (Fail, IO, List, Map, Nat, Parse)
import Std.Parse (char, nat, text)

def main(): {IO, Fail} () :=
  let lines := parseLines IO.readAll()
  IO.print "Part 1: ${solvePart1 lines}"
  IO.print "Part 2: ${solvePart2 lines}"

--| A grid point, `(x, y)`.
type Point = (Nat, Nat)

--| A line of vents, from one end to the other.
type Line = { x1: Nat, y1: Nat, x2: Nat, y2: Nat }

--| One line of vents per line of the input, `x1,y1 -> x2,y2`. A line that
--| isn't horizontal, vertical or diagonal at 45 degrees fails, naming it.
def parseLines (input: Text): {Fail} List Line := checkShapes (Parse.eachLine input Line.parse)

--| One line of vents, `x1,y1 -> x2,y2`.
def Line.parse(): {Parse} Line :=
  let x1 := nat()
  char ','
  let y1 := nat()
  text " -> "
  let x2 := nat()
  char ','
  let y2 := nat()
  { x1, y1, x2, y2 }

--| The lines, if each is horizontal, vertical or diagonal at 45 degrees;
--| otherwise fail, naming the first that isn't.
def checkShapes (lines: List Line): {Fail} List Line :=
  match firstBent lines with
    | Some (index, _) => Fail.fail "line ${index + 1} isn't horizontal, vertical or diagonal"
    | None => lines

--| The first line, with its index, that isn't horizontal, vertical or
--| diagonal at 45 degrees.
def firstBent (lines: List Line): Option (Nat, Line) :=
  lines.withIndex.find (((_, line)) => not (line.isStraight ∨ line.isDiagonal))

--| Horizontal or vertical.
def Line.isStraight (line: Line): Bool := line.x1 == line.x2 ∨ line.y1 == line.y2

--| Diagonal at 45 degrees: as far across as down.
def Line.isDiagonal (line: Line): Bool := Nat.absDiff line.x1 line.x2 == Nat.absDiff line.y1 line.y2

--| The coordinate `step` steps from `start` towards `stop`, one at a time.
def towards (start: Nat) (stop: Nat) (step: Nat): Nat :=
  if start < stop then start + step else if stop < start then start - step else start

--| The points a horizontal, vertical or diagonal line covers: from the
--| first end, a step at a time in each direction the line goes, to the
--| other end.
def Line.points (line: Line): List Point :=
  let steps := Nat.max (Nat.absDiff line.x1 line.x2) (Nat.absDiff line.y1 line.y2)
  List.range (steps + 1) |> .map (step => (towards line.x1 line.x2 step, towards line.y1 line.y2 step))

--| The number of points covered by at least two of the lines.
def overlaps (lines: List Line): Nat :=
  Map.counts (lines.flatMap Line.points) |> .count (_ times => 2 ≤ times)

--| Part 1: the horizontal and vertical lines only.
def solvePart1 (lines: List Line): Nat := overlaps (lines.filter Line.isStraight)

--| Part 2: every line.
def solvePart2 (lines: List Line): Nat := overlaps lines
