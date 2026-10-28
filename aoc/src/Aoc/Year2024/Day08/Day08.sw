-- Advent of Code 2024, day 8: antennas on a map, each tuned to a frequency.
-- Part 1 counts the locations on the map in line with two antennas of the
-- same frequency where one antenna is twice as far away as the other. Part 2
-- counts the locations in line with two antennas of the same frequency, at
-- any distance.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day08.main < inputs/2024/day08.txt
--
-- The proofs are in `Aoc.Year2024.Day08.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day08.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day08
import Std (Char, Fail, IO, Int, List, Nat, Option, Parse, Set, Text)

def main(): {IO, Fail} () :=
  let city := parseCity IO.readAll()
  IO.print "Part 1: ${solvePart1 city}"
  IO.print "Part 2: ${solvePart2 city}"

-- A grid point, on the map or off it, or the difference between two.
type Position = { row: Int, column: Int }

def Position.plus (position: Position) (other: Position): Position :=
  { row = position.row + other.row, column = position.column + other.column }

def Position.minus (position: Position) (other: Position): Position :=
  { row = position.row - other.row, column = position.column - other.column }

def Position.times (position: Position) (factor: Int): Position :=
  { row = position.row * factor, column = position.column * factor }

type Antenna = { frequency: Char, position: Position }

-- The map, `height` rows of `width` columns, and its antennas.
type City = { height: Nat, width: Nat, antennas: List Antenna }

-- One character of the map: `.` is empty, a letter or digit an antenna.
def cell(): {Parse} (Option Char) :=
  let char := Parse.satisfy "'.', a letter or a digit" (char => char == '.' || char.isAsciiAlphanumeric)
  if char == '.' then None else Some char

-- One row per line, all as long as the first.
def parseCity (input: Text): {Fail} City :=
  let rows := Parse.all input (() => Parse.grid cell)
  let width := rows.headOr [] |> .length
  let antennas :=
    rows.withIndex.flatMap (((row, cells)) =>
      Fail.ensure (cells.length == width) "line ${row + 1}: expected ${width} characters, as on the first line, got ${cells.length}"
      cells.withIndex.filterMap (((column, cell)) =>
        cell.map (frequency => ({ frequency, position = { row = row.toInt, column = column.toInt } }: Antenna))))
  { height = rows.length, width, antennas }

def City.contains (city: City) (position: Position): Bool :=
  0 <= position.row && position.row < city.height.toInt && 0 <= position.column && position.column < city.width.toInt

-- Every pair of two antennas with the same frequency, both ways round.
def City.antennaPairs (city: City): List (Position, Position) :=
  city.antennas
    |> .flatMap (antenna =>
      city.antennas
        |> .filter (other => antenna.frequency == other.frequency && antenna.position != other.position)
        |> .map (other => (antenna.position, other.position)))

-- The distinct positions on the map among `positions`.
def City.locations (city: City) (positions: List Position): Set Position := positions.filter city.contains |> Set.fromList

-- The points in line with `far` and `near` where `far` is twice as far away
-- as `near`: past `near`, and a third of the way from `near` to `far` when
-- that is a grid point.
def antinodesOf (far: Position) (near: Position): List Position :=
  let difference := near.minus far
  let past := near.plus difference
  if difference.row % 3 == 0 && difference.column % 3 == 0 then
    [past, near.minus { row = difference.row / 3, column = difference.column / 3 }]
  else [past]

-- Both parts divided by `divisor`, rounding down; unchanged for 0.
def Position.divideBy (position: Position): Nat → Position
  | Zero => position
  | Succ below =>
    let divisor := (Succ below).toInt
    { row = position.row / divisor, column = position.column / divisor }

-- The smallest step from `start` towards `end` that lands on grid points:
-- the difference divided by the greatest common divisor of its parts.
def Position.stepToward (start: Position) (end: Position): Position :=
  let difference := end.minus start
  difference.divideBy (Nat.gcd difference.row.natAbs difference.column.natAbs)

-- The grid points in line with `start` and `end`: whole steps from `start`
-- either way, as many as the map is high or wide, which reaches past it.
def City.harmonics (city: City) (start: Position) (end: Position): List Position :=
  let step := start.stepToward end
  List.range (Nat.max city.height city.width)
    |> .flatMap (count => [start.plus (step.times count.toInt), start.minus (step.times count.toInt)])

def solvePart1 (city: City): Nat :=
  city.antennaPairs |> .flatMap (((far, near)) => antinodesOf far near) |> city.locations |> .size

def solvePart2 (city: City): Nat :=
  city.antennaPairs |> .flatMap (((start, end)) => city.harmonics start end) |> city.locations |> .size
