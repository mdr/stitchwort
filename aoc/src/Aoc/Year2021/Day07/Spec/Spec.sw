--| Day 7 as the puzzle states it: the crabs all move to one position, each
--| paying fuel for its own distance, and the answer is the least total fuel
--| of any position. The proofs (Proofs/) show the program computes it, for
--| every input.
--|
--| What the spec decides:
--|
--| - The candidate positions are every `Nat`, not only those of crabs or
--|   those between them: the puzzle doesn't restrict where they may line
--|   up. Positions are horizontal positions, which the input gives as `Nat`s;
--|   a position left of 0 would be further than 0 from every crab, so leaving
--|   them out changes no answer.
--| - "The least fuel" is a number of fuel that some position costs and that
--|   no position beats (`LeastFuel`). There is at most one such number
--|   (`leastFuelUnique` in the proofs).
--| - With no crabs every position costs nothing, and the answer is 0.

namespace Aoc.Year2021.Day07.Spec
import Std (List, Nat)

--| A crab at `crab` moving to `position` takes as many steps as they are
--| apart.
def distance (crab position: Nat): Nat := if crab ≤ position then position - crab else crab - position

--| Part 1: "each change of 1 step in horizontal position of a single crab
--| costs 1 fuel".
def part1Fuel (steps: Nat): Nat := steps

--| Part 2: each step costs 1 more than the one before, the first costing 1,
--| so `steps` steps cost 1 + 2 + … + steps.
def part2Fuel (steps: Nat): Nat := (List.range 1 (steps + 1)).sum

--| The fuel every crab spends moving to `position`, added up.
def totalFuel (fuel: Nat → Nat) (crabs: List Nat) (position: Nat): Nat :=
  crabs.map (crab => fuel (distance crab position)) |> .sum

--| "The least fuel possible": some position costs `answer` in total, and no
--| position costs less.
def LeastFuel (fuel: Nat → Nat) (crabs: List Nat) (answer: Nat): Prop :=
  (exists (position: Nat) => totalFuel fuel crabs position = answer)
    ∧ (∀ (position: Nat) => answer ≤ totalFuel fuel crabs position)

def Part1Answer (crabs: List Nat) (answer: Nat): Prop := LeastFuel part1Fuel crabs answer

def Part2Answer (crabs: List Nat) (answer: Nat): Prop := LeastFuel part2Fuel crabs answer
