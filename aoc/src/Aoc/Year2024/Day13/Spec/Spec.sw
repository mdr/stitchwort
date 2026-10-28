-- Day 13 as the puzzle states it. The proofs (Proofs/) show the program
-- computes these: part 1 for every list of machines, part 2 for machines
-- whose buttons don't move the claw along the same line.

namespace Aoc.Year2024.Day13.Spec
import Aoc.Year2024.Day13 (Machine, Offset)
import Std (Int, List, Nat, Option)

-- "It costs 3 tokens to push the A button and 1 token to push the B button."
def cost (aPresses: Nat) (bPresses: Nat): Nat := 3 * aPresses + bPresses

-- "To win the prize, the claw must be positioned exactly above the prize on
-- both the X and Y axes": each press moves the claw by its button's amount.
def winsPrize (machine: Machine) (aPresses: Nat) (bPresses: Nat): Bool :=
  let a := machine.buttonA
  let b := machine.buttonB
  aPresses.toInt * a.x + bPresses.toInt * b.x == machine.prize.x && aPresses.toInt * a.y + bPresses.toInt * b.y == machine.prize.y

-- Part 1: "each button would need to be pressed no more than 100 times":
-- the cost of every winning pair of press counts from 0 to 100.
def winningCosts (machine: Machine): List Nat :=
  List.range 101
    |> .flatMap (aPresses =>
      List.range 101 |> .filter (bPresses => winsPrize machine aPresses bPresses) |> .map (bPresses => cost aPresses bPresses))

-- "The smallest number of tokens you would have to spend" to win this
-- machine's prize, if any presses win it.
def fewestTokens (machine: Machine): Option Nat := (winningCosts machine).minimum

-- "What is the fewest tokens you would have to spend to win all possible
-- prizes?": the machines that can't be won cost nothing.
def part1 (machines: List Machine): Nat := machines.sumBy (machine => (fewestTokens machine).getOrElse 0)

-- Part 2: "the position of every prize is actually 10000000000000 higher on
-- both the X and Y axis!"
def correctedMachine (machine: Machine): Machine := {
  buttonA = machine.buttonA,
  buttonB = machine.buttonB,
  prize = { x = machine.prize.x + 10000000000000, y = machine.prize.y + 10000000000000 }
}

-- With no limit on presses there are infinitely many counts to try, so the
-- fewest tokens is a statement: some presses win for `tokens`, and none win
-- for fewer.
def Fewest (machine: Machine) (tokens: Nat): Prop :=
  (∃ (aPresses: Nat) => ∃ (bPresses: Nat) => winsPrize machine aPresses bPresses = True ∧ cost aPresses bPresses = tokens)
    ∧ ((aPresses: Nat) → (bPresses: Nat) → winsPrize machine aPresses bPresses = True → tokens ≤ cost aPresses bPresses)

-- "There is no combination of A and B presses that will ever win a prize."
def Unwinnable (machine: Machine): Prop := (aPresses: Nat) → (bPresses: Nat) → winsPrize machine aPresses bPresses = False

-- The fewest tokens to win `machine`, or `None` when it can't be won.
def IsFewest (machine: Machine): Option Nat → Prop
  | Some tokens => Fewest machine tokens
  | None => Unwinnable machine

-- The answer to part 2 for `machines`: the sum of what `fewest` says each
-- corrected machine costs, for a `fewest` that is right about every one.
def Part2Answer (machines: List Machine) (answer: Nat): Prop :=
  ∃ (fewest: Machine → Option Nat) =>
    ((machine: Machine) → machine ∈ machines → IsFewest (correctedMachine machine) (fewest machine))
      ∧ answer = machines.sumBy (machine => (fewest machine).getOrElse 0)
