-- Day 10 as the puzzle states it, over the program's map: its heights
-- (`heightAt`) and its positions (`positions`). The proofs (Proofs/) show
-- the program computes these, for every map.

namespace Aoc.Year2024.Day10.Spec
import Aoc.Year2024.Day10 (..)
import Std (Bool, List, Nat, Option)

-- "Hiking trails never include diagonal steps - only up, down, left, or
-- right": one column apart in the same row, or one row apart in the same
-- column.
def isOrthogonalStep (from: Position) (to: Position): Bool :=
  (from.row == to.row && (from.column + 1 == to.column || to.column + 1 == from.column))
    || (from.column == to.column && (from.row + 1 == to.row || to.row + 1 == from.row))

-- "Always increases by a height of exactly 1 at each step".
def increasesByOne (map: TopographicMap) (from: Position) (to: Position): Bool :=
  match map.heightAt from with
    | Some height => map.heightAt to == Some (height + 1)
    | None => False

def isStep (map: TopographicMap) (from: Position) (to: Position): Bool := isOrthogonalStep from to && increasesByOne map from to

-- "A hiking trail is any path that starts at height 0, ends at height 9, and
-- always increases by a height of exactly 1 at each step."
def isHikingTrail (map: TopographicMap) (path: List Position): Bool :=
  (path.head |> .flatMap map.heightAt) == Some 0
    && (path.last |> .flatMap map.heightAt) == Some 9
    && path.zipWithNext.all (pair => isStep map pair.fst pair.snd)

-- Every list of `count` positions on the map, repeats allowed, each list
-- once.
def pathsOf (map: TopographicMap): (count: Nat) → List (List Position)
  | Zero => [Nil]
  | Succ count => map.positions |> .flatMap (position => pathsOf map count |> .map (Cons position))

-- The trails beginning at `start`: `start` and nine more positions, since a
-- trail climbs from 0 to 9 one height at a time. The proofs show every
-- trail is one of these (`trailsAreCandidates`).
def trailsFrom (map: TopographicMap) (start: Position): List (List Position) :=
  pathsOf map 9 |> .map (Cons start) |> .filter (isHikingTrail map)

-- "A trailhead is any position that starts one or more hiking trails".
def trailheads (map: TopographicMap): List Position := map.positions |> .filter (start => (trailsFrom map start).length >= 1)

-- "A trailhead's score is the number of 9-height positions reachable from
-- that trailhead via a hiking trail."
def score (map: TopographicMap) (trailhead: Position): Nat :=
  map.positions
    |> .count (nine => map.heightAt nine == Some 9 && (trailsFrom map trailhead).any (trail => trail.last == Some nine))

-- "A trailhead's rating is the number of distinct hiking trails which begin
-- at that trailhead."
def rating (map: TopographicMap) (trailhead: Position): Nat := (trailsFrom map trailhead).length

-- "The sum of the scores of all trailheads".
def part1 (map: TopographicMap): Nat := trailheads map |> .sumBy (score map)

-- "The sum of the ratings of all trailheads".
def part2 (map: TopographicMap): Nat := trailheads map |> .sumBy (rating map)
