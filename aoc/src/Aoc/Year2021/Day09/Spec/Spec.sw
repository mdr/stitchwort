--| Day 9 as the puzzle states it, over the program's height map: its
--| locations, each with its height (`cells`), and the height at a position
--| (`heightAt`, `None` off the map). The proofs (Proofs/) show the program
--| computes these answers, for every height map.

namespace Aoc.Year2021.Day09.Spec
import Aoc.Year2021.Day09 (..)
import Aoc.Common (Position, adjacent)
import Std (List, Nat, Option, Ord)

--| "Adjacent locations": up, down, left or right; diagonal locations don't
--| count. That is the shared grid code's `adjacent` (`Aoc.Common`): one
--| column apart in the same row, or one row apart in the same column.

--| "Low points: the locations that are lower than any of its adjacent
--| locations", each with its height. Locations on the edge or in a corner
--| have fewer adjacent locations.
def lowPoints (map: HeightMap): List (Position, Nat) := map.cells.filter (((at, height)) =>
  map.cells.all (((other, otherHeight)) => not (adjacent at other) || height < otherHeight))

--| "The risk level of a low point is 1 plus its height."
def riskLevel (height: Nat): Nat := 1 + height

--| Part 1: "the sum of the risk levels of all low points".
def part1 (map: HeightMap): Nat := (lowPoints map).sumBy (((_, height)) => riskLevel height)

--| "Locations of height 9 do not count as being in any basin."
def inSomeBasin (map: HeightMap) (position: Position): Bool := map.heightAt position |> .any (height => height != 9)

--| Steps from `from` to `to`: each step to an adjacent location that isn't
--| a 9 (`Aoc.Common.isPath`).
def isPath (map: HeightMap) (from: Position) (steps: List Position) (to: Position): Bool :=
  Aoc.Common.isPath (inSomeBasin map) from steps to

--| "A basin is all locations that eventually flow downward to a single low
--| point." Read as: the locations that aren't 9s and that can be reached
--| from the low point by steps between adjacent locations that aren't 9s,
--| the low point's connected area of non-9 locations. (The puzzle promises
--| that every location that isn't a 9 is in exactly one basin,
--| `EachInOneBasin` below. The answers below don't need the promise: it is
--| what makes a basin per low point the same as the connected areas.)
def InBasin (map: HeightMap) (low location: Position): Prop :=
  inSomeBasin map location = True ∧ ∃ (steps: List Position) => isPath map low steps location = True

--| "The size of a basin is the number of locations within the basin,
--| including the low point": `size` locations, with no repeats, exactly
--| those in the basin.
def BasinSize (map: HeightMap) (low: Position) (size: Nat): Prop :=
  ∃ (locations: List Position) => List.Distinct locations
    ∧ (∀ (location: Position) => location ∈ locations ↔ InBasin map low location)
    ∧ locations.length = size

--| "Multiply together the sizes of the three largest basins."
def threeLargestProduct (sizes: List Nat): Nat := sizes.sort [ord := Ord.reverse] |> .take 3 |> .product

--| Part 2's answer, with each low point's basin size given by `sizeOf`.
def Part2Answer (map: HeightMap) (answer: Nat): Prop :=
  ∃ (sizeOf: Position → Nat) => (∀ (low: Position) (height: Nat) => (low, height) ∈ lowPoints map
    → BasinSize map low (sizeOf low))
    ∧ answer = threeLargestProduct ((lowPoints map).map (((low, _)) => sizeOf low))

--| The puzzle's promise: each location that isn't a 9 is in the basin of
--| exactly one low point. Not assumed by the theorems; the tests check it
--| on the example and the input.
def EachInOneBasin (map: HeightMap): Prop :=
  ∀ (location: Position) => inSomeBasin map location = True
    → ∃ (low: Position) => ∃ (height: Nat) => (low, height) ∈ lowPoints map
      ∧ InBasin map low location
      ∧ (∀ (other: Position) (otherHeight: Nat) => (other, otherHeight) ∈ lowPoints map
        → InBasin map other location
        → other = low)
