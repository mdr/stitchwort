--| Advent of Code 2024, day 8: antennas on a map, each tuned to a frequency.
--| Part 1 counts the locations on the map in line with two antennas of the
--| same frequency where one antenna is twice as far away as the other. Part 2
--| counts the locations in line with two antennas of the same frequency, at
--| any distance.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day08.main < inputs/2024/day08.txt
--|
--| The proofs are in `Aoc.Year2024.Day08.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day08.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day08
import Aoc.Common (Offset, Position)
import Std (Char, Fail, IO, Int, List, Nat, Option, Parse, Set, Text, uncurry)

def main(): {IO, Fail} () :=
  let city := parseCity IO.readAll()
  IO.print "Part 1: ${solvePart1 city}"
  IO.print "Part 2: ${solvePart2 city}"

type Antenna = { frequency: Char, position: Position }

--| The map, `height` rows of `width` columns, and its antennas.
type City = { height: Nat, width: Nat, antennas: List Antenna }

--| One character of the map: `.` is empty, a letter or digit an antenna.
def cell(): {Parse} Option Char :=
  let char := Parse.satisfy "'.', a letter or a digit" (char => char == '.' || char.isAsciiAlphanumeric)
  if char == '.' then None else Some char

--| One row per line, all as long as the first.
def parseCity (input: Text): {Fail} City :=
  let grid := Parse.all input (() => Parse.grid cell)
  let rows := grid.toList.map .toList
  let width := grid.head.length
  let antennas := rows.withIndex.flatMap (((row, cells)) =>
    Fail.ensure
      (cells.length == width)
      "line ${row + 1}: expected ${width} characters, as on the first line, got ${cells.length}"
    cells.withIndex.filterMap (match some
      | (column, Some frequency) => ({ frequency, position = { row, column } }: Antenna)))
  { height = rows.length, width, antennas }

def City.contains (city: City) (position: Position): Bool := position.within city.height city.width

--| Every pair of two antennas with the same frequency, both ways round.
def City.antennaPairs (city: City): List (Position, Position) :=
  city.antennas
    |> .flatMap (antenna =>
      city.antennas
        |> .filter (other => antenna.frequency == other.frequency && antenna.position != other.position)
        |> .map (other => (antenna.position, other.position)))

--| The distinct positions on the map among `positions`.
def City.locations (city: City) (positions: List Position): Set Position := positions.filter city.contains |> .toSet

--| The points in line with `far` and `near` where `far` is twice as far away
--| as `near`: past `near` by the step from `far` to it, and a third of the
--| way back from `near` to `far` when that is a grid point. Those above or
--| left of the map are left out here, the rest past it by `locations`.
def antinodesOf (far near: Position): List Position :=
  let difference := near.minus far
  let steps :=
    if difference.rows % 3 == 0 && difference.columns % 3 == 0 then [difference, (divideBy difference 3).negate]
    else [difference]
  steps.filterMap near.offset

--| Both parts divided by `divisor`, rounding down.
def divideBy (offset: Offset) (divisor: Nat): Offset :=
  { rows = offset.rows / divisor.toInt, columns = offset.columns / divisor.toInt }

--| The smallest step from `start` towards `end` that lands on grid points:
--| the offset between them divided by the greatest common divisor of its
--| parts.
def Position.stepToward (start end: Position): Offset :=
  let difference := end.minus start
  divideBy difference (difference.rows.natAbs.gcd difference.columns.natAbs)

--| The grid points in line with `start` and `end`: whole steps from `start`
--| either way, as many as the map is high or wide, which reaches past it.
--| Those above or left of the map are left out here.
def City.harmonics (city: City) (start end: Position): List Position :=
  let step := start.stepToward end
  List.range 0 (Nat.max city.height city.width)
    |> .flatMap (count => [step.times count.toInt, (step.times count.toInt).negate] |> .filterMap start.offset)

def solvePart1 (city: City): Nat := city.antennaPairs |> .flatMap (uncurry antinodesOf) |> city.locations |> .size

def solvePart2 (city: City): Nat :=
  city.antennaPairs |> .flatMap (((start, end)) => city.harmonics start end) |> city.locations |> .size
