--| Day 5 as the puzzle states it: a line covers the grid points on it, from
--| one end to the other, and the answer is the number of points where at
--| least two lines overlap. The proofs (Proofs/) show the program computes
--| it, for every input.
--|
--| What the spec decides:
--|
--| - A line covers the grid points on the line segment between its ends,
--|   ends included. That is geometry, not a recipe: a point is on the
--|   segment when it lies within the rectangle the two ends span and is as
--|   far along the segment across as it is down. It holds for a line at any
--|   angle, and the puzzle's lines are horizontal, vertical or at 45
--|   degrees; part 2's theorem takes that as a hypothesis, since the
--|   program steps one point at a time in each direction and would miss
--|   points of a line at another angle (the parser rejects those).
--| - "The number of points": a count of a set of points, so a list of them
--|   without repeats, which has every such point and only those, has that
--|   many elements (std's `List.NumberWith`). Any two such lists have the
--|   same length (`List.numberWithUnique`), so it says what the number is.
--| - Several lines over the same stretch cover each point of it once each,
--|   and a line of one point (both ends the same) covers that point.

namespace Aoc.Year2021.Day05.Spec
import Aoc.Common (Line, Point)
import Std (List, Nat)

--| `b` is between `a` and `c`, either way round, ends included.
def between (a b c: Nat): Bool := Nat.min a c ≤ b ≤ Nat.max a c

--| "An entry like 1,1 -> 1,3 covers points 1,1, 1,2, and 1,3": the grid
--| points on the segment from one end to the other. A point is on it when it
--| is within the rectangle the ends span, and its distance across from the
--| first end is to its distance down as the segment's are to each other.
def covers (line: Line) (point: Point): Bool :=
  between line.from.x point.x line.to.x
    ∧ between line.from.y point.y line.to.y
    ∧ line.from.x.absDiff point.x * line.from.y.absDiff line.to.y
      == line.from.y.absDiff point.y * line.from.x.absDiff line.to.x

--| "Horizontal and vertical lines: lines where either x1 = x2 or y1 = y2."
def horizontalOrVertical (line: Line): Bool := line.from.x == line.to.x ∨ line.from.y == line.to.y

--| A diagonal line at exactly 45 degrees: as far across as down.
def diagonal (line: Line): Bool := line.from.x.absDiff line.to.x == line.from.y.absDiff line.to.y

--| How many of the lines cover the point.
def coveredBy (lines: List Line) (point: Point): Nat := lines.count (line => covers line point)

--| "A point where at least two lines overlap".
def overlap (lines: List Line) (point: Point): Bool := 2 ≤ coveredBy lines point

--| Part 1: "Consider only horizontal and vertical lines. At how many points
--| do at least two lines overlap?"
def Part1Answer (lines: List Line) (answer: Nat): Prop :=
  List.NumberWith answer (overlap (lines.filter horizontalOrVertical))

--| Part 2: the same, with every line.
def Part2Answer (lines: List Line) (answer: Nat): Prop := List.NumberWith answer (overlap lines)
