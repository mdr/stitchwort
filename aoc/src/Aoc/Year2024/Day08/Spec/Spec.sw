-- Day 8 as the puzzle states it. The proofs (Proofs/) show the program
-- computes these, for every city (part 2: whose antennas are on the map).

namespace Aoc.Year2024.Day08.Spec
import Aoc.Year2024.Day08 (..)
import Std (Bool, Int, List, Nat, Set)

-- Every location on the map.
def positions (city: City): List Position :=
  List.range city.height
    |> .flatMap (row => List.range city.width |> .map (column => ({ row = row.toInt, column = column.toInt }: Position)))

-- "Perfectly in line": the directions from `point` to `first` and to
-- `second` are parallel (their cross product is 0), or one of them is 0.
def inLine (point: Position) (first: Position) (second: Position): Bool :=
  let toFirst := first.minus point
  let toSecond := second.minus point
  toFirst.row * toSecond.column - toFirst.column * toSecond.row == 0

-- The square of the distance between two points.
def squaredDistance (from: Position) (to: Position): Int :=
  let difference := to.minus from
  difference.row * difference.row + difference.column * difference.column

-- "One of the antennas is twice as far away as the other": `far` is twice as
-- far from `point` as `near` is (compared squared, since distances are never
-- negative).
def twiceAsFar (point: Position) (far: Position) (near: Position): Bool :=
  squaredDistance point far == 4 * squaredDistance point near

-- Whether `holds` for some "two antennas of the same frequency", either way
-- round: two antennas, so at two different places.
def twoAntennas (city: City) (holds: Position → Position → Bool): Bool :=
  city.antennas.any (first =>
    city.antennas.any (second =>
      first.frequency == second.frequency && first.position != second.position && holds first.position second.position))

-- Part 1: "an antinode occurs at any point that is perfectly in line with two
-- antennas of the same frequency - but only when one of the antennas is twice
-- as far away as the other".
def isAntinode (city: City) (point: Position): Bool :=
  twoAntennas city (far near => inLine point far near && twiceAsFar point far near)

-- Part 2: "an antinode occurs at any grid position exactly in line with at
-- least two antennas of the same frequency, regardless of distance".
def isHarmonicAntinode (city: City) (point: Position): Bool := twoAntennas city (first second => inLine point first second)

-- "Unique locations within the bounds of the map" that `isAntinode`.
def antinodeLocations (city: City) (isAntinode: Position → Bool): Set Position := Set.fromList (positions city) |> .filter isAntinode

-- "How many unique locations within the bounds of the map contain an
-- antinode?"
def part1 (city: City): Nat := antinodeLocations city (isAntinode city) |> .size

def part2 (city: City): Nat := antinodeLocations city (isHarmonicAntinode city) |> .size
