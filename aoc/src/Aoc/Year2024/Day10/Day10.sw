-- Advent of Code 2024, day 10: a topographic map of heights 0 to 9. A
-- hiking trail starts at height 0, ends at height 9 and climbs by exactly 1
-- at each step, up, down, left or right. Part 1 adds up, over the trailheads
-- (the 0s), how many 9s each reaches by some trail; part 2 adds up how many
-- trails start at each.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day10.main < inputs/2024/day10.txt
--
-- The proofs are in `Aoc.Year2024.Day10.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day10.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day10
import Std (Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, digit)

def main(): {IO, Fail} () :=
  let map := parseMap IO.readAll()
  IO.print "Part 1: ${solvePart1 map}"
  IO.print "Part 2: ${solvePart2 map}"

type Position = { row: Nat, column: Nat }

-- The heights, row by row; `None` is an impassable tile, `.`, which only
-- the puzzle's small examples have.
type TopographicMap = { rows: List (List (Option Nat)) }

-- One tile: a height, or `.`.
def tile(): {Parse} (Option Nat) :=
  Parse.oneOf [
    () => Some digit().toNat,
    () =>
      char '.'
      None
  ]

-- One row per line, all as long as the first.
def parseMap (input: Text): {Fail} TopographicMap :=
  let rows := Parse.all input (() => Parse.grid tile)
  let width := rows.headOr [] |> .length
  rows.withIndex |> .map (((row, tiles)) =>
    Fail.ensure (tiles.length == width) "line ${row + 1}: expected ${width} tiles, as on the first line, got ${tiles.length}")
  { rows }

-- The height at `position`; `None` off the map or on an impassable tile.
def TopographicMap.heightAt (map: TopographicMap) (position: Position): Option Nat :=
  map.rows.getOr position.row Nil |> .getOr position.column None

-- Every position of the map, row by row.
def TopographicMap.positions (map: TopographicMap): List Position :=
  List.range map.rows.length
    |> .flatMap (row => List.range (map.rows.getOr row Nil).length |> .map (column => ({ row, column }: Position)))

-- The grid point one step up, if there is one: none above the top row.
def Position.above (position: Position): List Position :=
  match position.row with
    | Zero => Nil
    | Succ up => [{ position | row = up }]

-- The grid point one step left, if there is one.
def Position.leftOf (position: Position): List Position :=
  match position.column with
    | Zero => Nil
    | Succ previous => [{ position | column = previous }]

-- The grid points one step right and one step down.
def Position.rightAndBelow (position: Position): List Position :=
  [{ position | column = position.column + 1 }, { position | row = position.row + 1 }]

-- The grid points one step up, left, right and down.
def Position.neighbours (position: Position): List Position := position.above ++ position.leftOf ++ position.rightAndBelow

-- `to` is exactly one higher than `from`.
def TopographicMap.isOneHigher (map: TopographicMap) (from: Position) (to: Position): Bool :=
  match map.heightAt from with
    | Some height => map.heightAt to == Some (height + 1)
    | None => False

-- The neighbours a trail can step to from `position`.
def TopographicMap.uphill (map: TopographicMap) (position: Position): List Position :=
  position.neighbours |> .filter (map.isOneHigher position)

-- Where the trails from `position` end after `steps` more steps uphill: one
-- entry per trail, so a 9 two trails reach is there twice.
def TopographicMap.trailEnds (map: TopographicMap): (steps: Nat) → (position: Position) → List Position
  | Zero, position => if map.heightAt position == Some 9 then [position] else Nil
  | Succ steps, position => map.uphill position |> .flatMap (map.trailEnds steps)

-- The positions of height 0.
def TopographicMap.trailheads (map: TopographicMap): List Position := map.positions |> .filter (position => map.heightAt position == Some 0)

-- A trailhead's score: the distinct 9s its trails reach, nine steps up.
def TopographicMap.score (map: TopographicMap) (trailhead: Position): Nat := map.trailEnds 9 trailhead |> .distinct |> .length

-- A trailhead's rating: its trails, one end each.
def TopographicMap.rating (map: TopographicMap) (trailhead: Position): Nat := map.trailEnds 9 trailhead |> .length

def solvePart1 (map: TopographicMap): Nat := map.trailheads |> .sumBy map.score

def solvePart2 (map: TopographicMap): Nat := map.trailheads |> .sumBy map.rating
