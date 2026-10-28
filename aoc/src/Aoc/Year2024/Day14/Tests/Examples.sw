-- Day 14's tests: the example from the puzzle, unit tests, and small
-- generated inputs whose answers were computed separately in Python. Kept
-- apart from the program, so `stitchwort run Aoc.Year2024.Day14.main`
-- doesn't check them.

namespace Aoc.Year2024.Day14.Tests
import Aoc.Year2024.Day14 (..)
import Aoc.Year2024.Day14.Spec (after, isBottom, isLeft, isRight, isTop, part1)
import Std (Fail, IO, List, Nat, Option, Pair, Result, Text)

def parsed (input: Text): Result (List Robot) Text := Fail.toResult (() => parseRobots input)

def robotsOf (input: Text): List Robot := Fail.orElse [] (() => parseRobots input)

def example: Text := """
  p=0,4 v=3,-3
  p=6,3 v=-1,-3
  p=10,3 v=-1,2
  p=2,0 v=2,-1
  p=0,0 v=1,3
  p=3,0 v=-2,-2
  p=7,6 v=-1,-3
  p=3,0 v=-1,-2
  p=9,3 v=2,3
  p=7,3 v=-1,2
  p=2,4 v=2,-3
  p=9,5 v=-3,-3
  """

def exampleSpace: Space := Space.of 11 7

def puzzleSpace: Space := Space.of 101 103

def tile (x: Nat) (y: Nat): Position := { x, y }

def robotAt (x: Nat) (y: Nat) (dx: Int) (dy: Int): Robot := { position = { x, y }, velocity = { x = dx, y = dy } }

test "example, part 1" := solvePart1 exampleSpace (robotsOf example) == 12
test "example, part 2: two robots share 3,0 at the start" := solvePart2 exampleSpace (robotsOf example) == Some 1
test "example, the spec's part 1" := part1 exampleSpace (robotsOf example) == 12

-- "the quadrants contain 1, 3, 4, and 1 robot".
test "example, the quadrant counts" :=
  let inQuadrants := exampleSpace.positionsAfter 100 (robotsOf example) |> .filterMap exampleSpace.quadrantOf
  quadrants.map (quadrant => inQuadrants.count (== quadrant)) == [1, 3, 4, 1]

test "example, the tiles after 100 seconds" :=
  exampleSpace.positionsAfter 100 (robotsOf example) |> .sortOn (position => (position.y, position.x)) == [
    tile 6 0,
    tile 6 0,
    tile 9 0,
    tile 0 2,
    tile 1 3,
    tile 2 3,
    tile 5 4,
    tile 3 5,
    tile 4 5,
    tile 4 5,
    tile 1 6,
    tile 6 6
  ]

-- "Here is what robot p=2,4 v=2,-3 does for the first few seconds".
test "the puzzle's robot, second by second" :=
  [0, 1, 2, 3, 4, 5].map (seconds => exampleSpace.positionAfter seconds (robotAt 2 4 2 (-3)))
    == [tile 2 4, tile 4 1, tile 6 5, tile 8 2, tile 10 6, tile 1 3]
test "the spec's robot, one tile at a time" :=
  [0, 1, 2, 3, 4, 5].all (seconds => after exampleSpace seconds (robotAt 2 4 2 (-3)) == exampleSpace.positionAfter seconds (robotAt 2 4 2 (-3)))

test "a negative velocity wraps to the far edge" := exampleSpace.positionAfter 1 (robotAt 0 0 (-1) (-1)) == tile 10 6
test "a velocity of more than the width wraps more than once" :=
  exampleSpace.positionAfter 1 (robotAt 3 2 (-25) 15) == tile 0 3 && after exampleSpace 1 (robotAt 3 2 (-25) 15) == tile 0 3
test "a velocity of the width stays put" := exampleSpace.positionAfter 7 (robotAt 4 2 11 (-7)) == tile 4 2
test "no seconds" := exampleSpace.positionAfter 0 (robotAt 4 2 3 3) == tile 4 2
test "back after width times height seconds" :=
  (robotsOf example).all (robot => exampleSpace.positionAfter 77 robot == robot.position)

test "the middle column is in no quadrant" := [0, 1, 2, 3, 4, 5, 6].all (y => exampleSpace.quadrantOf (tile 5 y) == None)
test "the middle row is in no quadrant" := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10].all (x => exampleSpace.quadrantOf (tile x 3) == None)
test "the tiles beside the middle" :=
  exampleSpace.quadrantOf (tile 4 2) == Some TopLeft
    && exampleSpace.quadrantOf (tile 6 2) == Some TopRight
    && exampleSpace.quadrantOf (tile 4 4) == Some BottomLeft
    && exampleSpace.quadrantOf (tile 6 4) == Some BottomRight
test "the corners" :=
  [tile 0 0, tile 100 0, tile 0 102, tile 100 102].map puzzleSpace.quadrantOf == [Some TopLeft, Some TopRight, Some BottomLeft, Some BottomRight]
test "the spec's halves agree on the edge cases" :=
  [tile 4 2, tile 5 2, tile 6 3, tile 0 6, tile 10 0].all (position =>
    (exampleSpace.quadrantOf position == Some TopLeft) == (isTop exampleSpace position && isLeft exampleSpace position)
      && (exampleSpace.quadrantOf position == Some BottomRight) == (isBottom exampleSpace position && isRight exampleSpace position))
test "everyone in the middle is a safety factor of 0" := exampleSpace.safetyFactor [tile 5 0, tile 0 3, tile 5 3] == 0
test "an empty quadrant makes 0" := exampleSpace.safetyFactor [tile 0 0, tile 10 0, tile 0 6] == 0
test "one robot in each quadrant" := exampleSpace.safetyFactor [tile 0 0, tile 10 0, tile 0 6, tile 10 6, tile 10 6] == 2

test "no overlap" := noOverlap [tile 0 0, tile 1 0, tile 0 1]
test "an overlap" := !noOverlap [tile 0 0, tile 1 0, tile 0 0]
test "no robots don't overlap" := noOverlap []
test "a robot already in place" := solvePart2 exampleSpace [robotAt 0 0 1 1] == Some 0
test "the period is width times height" := exampleSpace.period == 77 && puzzleSpace.period == 10403

-- Generated with Python's `random` (seed 1): 15 robots on the example's
-- space, some with velocities of the full width; Python gives 64 and 3.
def generatedSmall: Text := """
  p=2,4 v=-9,-3
  p=1,3 v=3,0
  p=10,3 v=-5,-6
  p=7,0 v=1,-1
  p=9,6 v=-11,4
  p=7,2 v=-4,2
  p=1,2 v=-11,-7
  p=0,5 v=6,-7
  p=6,5 v=-5,-1
  p=0,4 v=-4,5
  p=7,3 v=6,-4
  p=5,1 v=10,-4
  p=7,2 v=-11,-1
  p=8,5 v=-8,-5
  p=10,5 v=-2,-6
  """

test "generated, 15 robots" :=
  solvePart1 exampleSpace (robotsOf generatedSmall) == 64 && solvePart2 exampleSpace (robotsOf generatedSmall) == Some 3

-- Seed 2: 40 robots on the 77 tiles never all on different tiles; Python
-- gives 3564 and none.
def generatedCrowded: Text := """
  p=0,0 v=-9,-2
  p=2,5 v=10,6
  p=4,2 v=8,-4
  p=9,0 v=7,3
  p=2,3 v=9,-1
  p=8,2 v=6,7
  p=7,4 v=-3,7
  p=0,6 v=-11,-2
  p=7,2 v=1,-1
  p=8,1 v=6,-5
  p=3,1 v=-11,-5
  p=5,1 v=-7,1
  p=8,2 v=5,3
  p=8,1 v=3,5
  p=6,5 v=5,7
  p=5,6 v=7,-2
  p=5,6 v=3,-5
  p=6,5 v=3,3
  p=8,1 v=4,-3
  p=7,4 v=5,6
  p=5,5 v=3,7
  p=7,2 v=7,4
  p=8,5 v=3,0
  p=10,1 v=-1,6
  p=2,4 v=-3,5
  p=7,2 v=-2,5
  p=8,4 v=5,1
  p=10,4 v=7,-1
  p=4,5 v=-5,0
  p=8,2 v=10,2
  p=1,6 v=-1,4
  p=0,6 v=-5,4
  p=1,0 v=7,3
  p=0,2 v=7,-4
  p=10,0 v=5,-5
  p=4,1 v=-5,7
  p=0,3 v=11,5
  p=0,0 v=0,-2
  p=2,1 v=10,-7
  p=1,0 v=-9,-7
  """

test "generated, 40 robots, never apart" :=
  solvePart1 exampleSpace (robotsOf generatedCrowded) == 3564 && solvePart2 exampleSpace (robotsOf generatedCrowded) == None

-- Seed 3: 30 robots on the puzzle's space; Python gives 2200 and 0.
def generatedLarge: Text := """
  p=30,75 v=38,-70
  p=47,77 v=20,57
  p=74,8 v=54,-100
  p=60,33 v=40,-44
  p=24,91 v=19,35
  p=70,60 v=0,60
  p=19,29 v=61,-65
  p=66,49 v=88,-100
  p=85,99 v=-85,-63
  p=97,75 v=-91,-26
  p=99,3 v=-33,18
  p=76,92 v=-2,79
  p=100,54 v=0,83
  p=73,56 v=-67,-10
  p=12,4 v=-67,23
  p=27,33 v=71,8
  p=99,80 v=-24,4
  p=64,49 v=45,-14
  p=68,74 v=3,46
  p=29,43 v=73,-96
  p=35,77 v=70,75
  p=20,89 v=-18,35
  p=73,72 v=-75,79
  p=83,27 v=61,43
  p=34,36 v=-70,-87
  p=61,81 v=22,-81
  p=44,102 v=-84,2
  p=19,2 v=-26,6
  p=98,53 v=-71,-92
  p=77,78 v=93,-92
  """

test "generated, 30 robots on the puzzle's space" :=
  solvePart1 puzzleSpace (robotsOf generatedLarge) == 2200 && solvePart2 puzzleSpace (robotsOf generatedLarge) == Some 0
test "generated, the spec agrees after 100 seconds" := part1 puzzleSpace (robotsOf generatedLarge) == 2200

test "parse" := parsed "p=0,4 v=3,-3\np=10,3 v=-1,2\n" == Ok [robotAt 0 4 3 (-3), robotAt 10 3 (-1) 2]
test "parse without a final line break" := parsed "p=0,4 v=3,-3" == Ok [robotAt 0 4 3 (-3)]
test "a negative position" := parsed "p=-1,4 v=3,-3\n" == Err "line 1, column 3: expected a number, got '-'"
test "a missing velocity" := parsed "p=1,4\n" == Err "line 1, column 6: expected ' v=', got the end of the line"
test "a bad number" := parsed "p=1,4 v=3,x\n" == Err "line 1, column 11: expected a number, got 'x'"

-- What the example's `main` prints and how it ends, for some input lines.
def ran (lines: List Text): Pair (List Text) (Result Bool Text) :=
  IO.simulate lines (() => Result.map (Fail.toResult mainExample) (unit => True))

test "main on the example" := ran (example.lines) == MkPair ["Part 1: 12", "Part 2: 1"] (Ok True)
test "main with a robot outside the space" := ran ["p=0,0 v=1,1", "p=11,0 v=1,1"] == MkPair [] (Err "line 2: the robot starts outside the space")
test "main with no picture" := ran (generatedCrowded.lines) == MkPair ["Part 1: 3564", "Part 2: none"] (Ok True)
