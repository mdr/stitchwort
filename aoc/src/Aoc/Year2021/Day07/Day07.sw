--| Advent of Code 2021, day 7: crabs in submarines sit at horizontal
--| positions (one line of numbers, comma-separated) and must all move to the
--| same position. Moving costs fuel; the answer is the least total fuel at
--| which they can line up. In part 1 each step costs one unit of fuel; in
--| part 2 a crab's first step costs 1, its second 2, and so on, so `n` steps
--| cost 1 + 2 + … + n.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day07.main < inputs/2021/day07.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| The program tries every position from the leftmost crab to the rightmost
--| and keeps the least total: a position further out is further from every
--| crab than the end crab's, so it costs at least as much. Part 2's cost of
--| `n` steps is Gauss's sum, `Nat.sumBetween 1 n`. The proofs, that both
--| answers are the least total fuel over every position, for every input,
--| are in `Aoc.Year2021.Day07.Proofs` (Proofs/), and the tests in
--| `Aoc.Year2021.Day07.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2021.Day07
import Std (Fail, IO, List, Nat, Parse)
import Std.Parse (char, nat, sepBy1)

def main(): {IO, Fail} () :=
  let crabs := parseCrabs IO.readAll()
  IO.print "Part 1: ${solvePart1 crabs}"
  IO.print "Part 2: ${solvePart2 crabs}"

--| The crabs' positions, `16,1,2,0,4`, on one line. Anything else fails,
--| naming the line and column.
def parseCrabs (input: Text): {Fail} List Nat := Parse.all input (() => sepBy1 nat (() => char ','))

--| The fuel to move a crab `steps` steps, in part 1: one a step.
def stepFuel (steps: Nat): Nat := steps

--| ... and in part 2: 1 + 2 + … + steps.
def growingFuel (steps: Nat): Nat := Nat.sumBetween 1 steps

--| The fuel for every crab to move to `position`.
def fuelAt (fuel: Nat → Nat) (crabs: List Nat) (position: Nat): Nat :=
  crabs.sumBy (crab => fuel (Nat.absDiff crab position))

--| The rightmost crab's position (0 when there are none), and the leftmost's
--| (the rightmost's when there are none).
def rightmost (crabs: List Nat): Nat := crabs.foldLeft 0 Nat.max

def leftmost (crabs: List Nat): Nat := crabs.foldLeft (rightmost crabs) Nat.min

--| The least total fuel over the positions from the leftmost crab to the
--| rightmost.
def leastFuel (fuel: Nat → Nat) (crabs: List Nat): Nat :=
  match List.between (leftmost crabs) (rightmost crabs) |> .map (fuelAt fuel crabs) |> .minimum with
    | Some least => least
    | None => 0

def solvePart1 (crabs: List Nat): Nat := leastFuel stepFuel crabs

def solvePart2 (crabs: List Nat): Nat := leastFuel growingFuel crabs
