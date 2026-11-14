--| Advent of Code 2020, day 3: a map of open squares (`.`) and trees (`#`)
--| that repeats to the right without end. A toboggan starts at the top left
--| and moves on a slope, so many columns right and rows down at each step,
--| until it goes past the bottom. Part 1 counts the trees it meets on the
--| slope right 3, down 1; part 2 multiplies the counts on five slopes.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day03.main < inputs/2020/day03.txt
--|
--| The proofs, that the counts are the trees on the puzzle's path through the
--| repeating map, are in `Aoc.Year2020.Day03.Proofs` (Proofs/), and the tests
--| in `Aoc.Year2020.Day03.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2020.Day03
import Aoc.Common (Grid, Position, parseGrid)
import Std (Char, Fail, IO, List, Nat, Parse, Text)

def main(): {IO, Fail} () :=
  let map := parseMap IO.readAll()
  IO.print "Part 1: ${solvePart1 map}"
  IO.print "Part 2: ${solvePart2 map}"

type Square = | Open | Tree

--| The two characters a map is drawn with.
def isSquare (char: Char): Bool := char == '.' || char == '#'

--| `#` is a tree, `.` an open square.
def Square.ofChar (char: Char): Square := if char == '#' then Tree else Open

def square(): {Parse} Square := Square.ofChar (Parse.satisfy "'.' or '#'" isSquare)

--| One row of the map per line, every row as long as the first.
def parseMap (input: Text): {Fail} Grid Square := parseGrid input square

--| How far the toboggan moves at each step.
type Slope = { right: Nat, down: Nat }

--| The trees at each step on `slope` from the top left, the first step's
--| square onwards, until a step goes past the bottom.
def treesOn (map: Grid Square) (slope: Slope): Nat :=
  let find := map.lookupOr Open
  List.rangeFrom (count := map.height) (start := 1)
    |> .takeWhile (step => step * slope.down < map.height)
    |> .count (step => find { row = step * slope.down, column = step * slope.right % map.width } == Tree)

def solvePart1 (map: Grid Square): Nat := treesOn map { right = 3, down = 1 }

def slopes: List Slope := [
  { right = 1, down = 1 },
  { right = 3, down = 1 },
  { right = 5, down = 1 },
  { right = 7, down = 1 },
  { right = 1, down = 2 }
]

def solvePart2 (map: Grid Square): Nat := slopes.map (treesOn map) |> List.product
