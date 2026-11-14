--| Advent of Code 2024, day 13: claw machines, each with two buttons that
--| move the claw by fixed amounts and a prize at some position. Pressing A
--| costs 3 tokens and B 1. Part 1 adds up the fewest tokens that win each
--| prize that can be won with at most 100 presses of each button; part 2
--| moves every prize 10000000000000 further along both axes, with no limit
--| on presses.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day13.main < examples/2024/day13.txt
--|
--| The proofs are in `Aoc.Year2024.Day13.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day13.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day13
import Aoc.Common (Coords, Unoriented)
import Std (Fail, IO, Int, List, Nat, Option, Parse, Text, uncurry)
import Std.Parse (nat, newline, sections, text)

def main(): {IO, Fail} () :=
  let machines := parseMachines IO.readAll()
  IO.print "Part 1: ${solvePart1 machines}"
  IO.print "Part 2: ${solvePart2 machines}"

--| How far a button moves the claw, or how far the prize is from where the
--| claw starts: `Unoriented`, as the puzzle has no up.
type Machine = { buttonA: Coords Unoriented, buttonB: Coords Unoriented, prize: Coords Unoriented }

--| "X+94, Y+34" for a button, "X=8400, Y=5400" for the prize: `sign` is the
--| "+" or the "=".
def offset (sign: Text): {Parse} Coords Unoriented :=
  text "X${sign}"
  let x := nat()
  text ", Y${sign}"
  let y := nat()
  { x = x.toInt, y = y.toInt }

--| Three lines: button A, button B and the prize.
def clawMachine(): {Parse} Machine :=
  text "Button A: "
  let buttonA := offset "+"
  newline()
  text "Button B: "
  let buttonB := offset "+"
  newline()
  text "Prize: "
  let prize := offset "="
  { buttonA, buttonB, prize }

--| Machines separated by blank lines.
def parseMachines (input: Text): {Fail} List Machine := Parse.all input (() => sections clawMachine |> .toList)

--| What pressing A `aPresses` times and B `bPresses` times costs.
def tokens (aPresses bPresses: Nat): Nat := 3 * aPresses + bPresses

--| Whether those presses put the claw exactly over the prize.
def Machine.wins (machine: Machine) (aPresses bPresses: Nat): Bool :=
  aPresses.toInt * machine.buttonA.x + bPresses.toInt * machine.buttonB.x == machine.prize.x
    && aPresses.toInt * machine.buttonA.y + bPresses.toInt * machine.buttonB.y == machine.prize.y

--| 0 exactly when the buttons move the claw along the same line.
def Machine.determinant (machine: Machine): Int :=
  machine.buttonA.x * machine.buttonB.y - machine.buttonA.y * machine.buttonB.x

--| Cramer's rule: with a nonzero determinant, the two equations have one
--| solution, and these are its presses if they are whole and not negative.
def Machine.onlyPresses (machine: Machine) (nonzero: machine.determinant ≠ 0): Option (Nat, Nat) :=
  let prize := machine.prize
  let aPresses := (prize.x * machine.buttonB.y - prize.y * machine.buttonB.x) / machine.determinant
  let bPresses := (machine.buttonA.x * prize.y - machine.buttonA.y * prize.x) / machine.determinant
  Option.map2 (a b => (a, b)) aPresses.toNatChecked bPresses.toNatChecked |> .filter (((a, b)) => machine.wins a b)

--| The fewest tokens over every press count up to `limit` for each button.
def Machine.searchTokens (machine: Machine) (limit: Nat): Option Nat :=
  List.range 0 (limit + 1)
    |> .flatMap (aPresses => List.range 0 (limit + 1) |> .filter (machine.wins aPresses) |> .map (tokens aPresses))
    |> .minimum

--| The fewest tokens that win with at most `limit` presses of each button.
--| Buttons along the same line may have many solutions, so they are searched.
def Machine.fewestTokensWithin (machine: Machine) (limit: Nat): Option Nat :=
  if nonzero: machine.determinant ≠ 0 then
    machine.onlyPresses nonzero
      |> .filter (((aPresses, bPresses)) => aPresses ≤ limit && bPresses ≤ limit)
      |> .map (uncurry tokens)
  else machine.searchTokens limit

--| How many presses of a button that moves the claw `step` move it exactly
--| `distance`, if some number does.
def pressesToCover (step distance: Coords Unoriented): Option Nat :=
  let count := if step.x ≠ 0 then distance.x / step.x else if step.y ≠ 0 then distance.y / step.y else 0
  if count * step.x == distance.x && count * step.y == distance.y then count.toNatChecked else None

--| The prize's offset after `presses` of a button that moves the claw `step`.
def Machine.remaining (machine: Machine) (step: Coords Unoriented) (presses: Nat): Coords Unoriented :=
  machine.prize.minus (step.times presses.toInt)

--| The fewest tokens for buttons along the same line. Swapping presses of
--| one button for presses of the other that move the claw as far keeps a
--| win, so the cheapest win presses A fewer times than B moves along an
--| axis, or B fewer times than A does: try those counts.
def Machine.collinearTokens (machine: Machine): Option Nat :=
  let buttonA := machine.buttonA
  let buttonB := machine.buttonB
  let fewerA :=
    List.range 0 (Nat.max buttonB.x.natAbs buttonB.y.natAbs + 1)
      |> .filterMap (aPresses => pressesToCover buttonB (machine.remaining buttonA aPresses) |> .map (tokens aPresses))
  let fewerB :=
    List.range 0 (Nat.max buttonA.x.natAbs buttonA.y.natAbs + 1)
      |> .filterMap (bPresses =>
        pressesToCover buttonA (machine.remaining buttonB bPresses) |> .map (aPresses => tokens aPresses bPresses))
  (fewerA ++ fewerB).minimum

--| The fewest tokens that win, with no limit on presses.
def Machine.fewestTokens (machine: Machine): Option Nat :=
  if nonzero: machine.determinant ≠ 0 then machine.onlyPresses nonzero |> .map (uncurry tokens)
  else machine.collinearTokens

--| Part 2's prize, 10000000000000 further along both axes.
def Machine.corrected (machine: Machine): Machine :=
  { machine | prize = machine.prize.plus { x = 10000000000000, y = 10000000000000 } }

def solvePart1 (machines: List Machine): Nat :=
  machines.sumBy (machine => machine.fewestTokensWithin 100 |> .getOrElse 0)

def solvePart2 (machines: List Machine): Nat :=
  machines.sumBy (machine => machine.corrected |> .fewestTokens |> .getOrElse 0)
