--| Advent of Code 2024, day 10: a topographic map of heights 0 to 9. A hiking
--| trail starts at height 0, ends at height 9 and climbs by exactly 1 at each
--| step, up, down, left or right. Part 1 adds up, over the trailheads (the
--| 0s), how many 9s each reaches by some trail; part 2 adds up how many
--| trails start at each.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day10.main < inputs/2024/day10.txt
--|
--| The proofs are in `Aoc.Year2024.Day10.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day10.Tests` (Tests/); `run` checks neither. Positions,
--| their neighbours (up, right, down and left), lookups and
--| the parser are the shared grid code's (`Aoc.Common`, Common/Grid.sw).

namespace Aoc.Year2024.Day10
import Aoc.Common (Grid, Position, parseGrid)
import Std (Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (char, digit)

def main(): {IO, Fail} () :=
  let map := parseMap IO.readAll()
  IO.print "Part 1: ${solvePart1 map}"
  IO.print "Part 2: ${solvePart2 map}"

--| The heights; `None` is an impassable tile, `.`, which only the puzzle's
--| small examples have.
type TopographicMap = { grid: Grid (Option Nat) }

--| One tile: a height, or `.`.
def tile(): {Parse} Option Nat := Parse.oneOf [
  () => Some digit().toNat,
  () =>
    char '.'
    None
]

--| One row of tiles per line, every row as long as the first (the puzzle's
--| map is a rectangle; `parseGrid` checks it).
def parseMap (input: Text): {Fail} TopographicMap := { grid = parseGrid input tile }

--| The height at `position`; `None` off the map or on an impassable tile.
def TopographicMap.heightAt (map: TopographicMap) (position: Position): Option Nat := map.grid.at position |> .flatten

--| Every position of the map, row by row.
def TopographicMap.positions (map: TopographicMap): List Position := map.grid.cells |> .map Pair.fst

--| `to` is exactly one higher than `from`.
def TopographicMap.isOneHigher (map: TopographicMap) (from to: Position): Bool := match map.heightAt from with
  | Some height => map.heightAt to == Some (height + 1)
  | None => False

--| The neighbours a trail can step to from `position`.
def TopographicMap.uphill (map: TopographicMap) (position: Position): List Position :=
  position.neighbours |> .filter (map.isOneHigher position)

--| Where the trails from `position` end after `steps` more steps uphill: one
--| entry per trail, so a 9 two trails reach is there twice.
def TopographicMap.trailEnds (map: TopographicMap): (steps: Nat) → (position: Position) → List Position
  | Zero, position => if map.heightAt position == Some 9 then [position] else []
  | Succ steps, position => map.uphill position |> .flatMap (map.trailEnds steps)

--| The positions of height 0.
def TopographicMap.trailheads (map: TopographicMap): List Position :=
  map.positions |> .filter (position => map.heightAt position == Some 0)

--| A trailhead's score: the distinct 9s its trails reach, nine steps up.
def TopographicMap.score (map: TopographicMap) (trailhead: Position): Nat :=
  map.trailEnds 9 trailhead |> .unique |> .length

--| A trailhead's rating: its trails, one end each.
def TopographicMap.rating (map: TopographicMap) (trailhead: Position): Nat := map.trailEnds 9 trailhead |> .length

def solvePart1 (map: TopographicMap): Nat := map.trailheads |> .sumBy map.score

def solvePart2 (map: TopographicMap): Nat := map.trailheads |> .sumBy map.rating
