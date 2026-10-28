-- Advent of Code 2024, day 11: a line of numbered stones. Each blink, every
-- stone changes by the first rule that applies: 0 becomes 1, a number with an
-- even number of digits splits into its left and right halves, and any other
-- is multiplied by 2024. Part 1 counts the stones after 25 blinks, part 2
-- after 75.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day11.main < inputs/2024/day11.txt
--
-- The proofs are in `Aoc.Year2024.Day11.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day11.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day11
import Std (Fail, IO, List, Map, Nat, Parse, Text)
import Std.Parse (nat, sepBy1, spaces1)

def main(): {IO, Fail} () :=
  let stones := parseStones IO.readAll()
  IO.print "Part 1: ${solvePart1 stones}"
  IO.print "Part 2: ${solvePart2 stones}"

-- The numbers on the stones, left to right, separated by spaces.
def parseStones (input: Text): {Fail} (List Nat) := Parse.all input (() => sepBy1 nat spaces1)

-- What one stone becomes after a blink, left to right.
def changeStone (stone: Nat): List Nat :=
  if stone == 0 then [1]
  else
    let digitCount := stone.digitCount
    if digitCount % 2 == 0 then
      let place := Nat.pow 10 (digitCount / 2)
      [stone / place, stone % place]
    else [stone * 2024]

-- `counts` with `count` more stones of each number in `stones`.
def addStones (counts: Map Nat Nat) (stones: List Nat) (count: Nat): Map Nat Nat :=
  stones.foldLeft counts (counts stone => counts.insertWith stone count Nat.add)

-- A blink on how many stones show each number: every stone with the same
-- number changes the same way.
def blinkCounts (counts: Map Nat Nat): Map Nat Nat :=
  counts.foldLeft Map.empty (blinked stone count => addStones blinked (changeStone stone) count)

-- How many stones there are after `blinks` blinks.
def countAfter (blinks: Nat) (stones: List Nat): Nat :=
  blinks.iterate blinkCounts (Map.counts stones) |> .values |> .sum

def solvePart1 (stones: List Nat): Nat := countAfter 25 stones

def solvePart2 (stones: List Nat): Nat := countAfter 75 stones
