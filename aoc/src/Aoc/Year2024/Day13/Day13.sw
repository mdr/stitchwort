-- Advent of Code 2024, day 13: claw machines, each with two buttons that
-- move the claw by fixed amounts and a prize at some position. Pressing A
-- costs 3 tokens and B 1. Part 1 adds up the fewest tokens that win each
-- prize that can be won with at most 100 presses of each button; part 2
-- moves every prize 10000000000000 further along both axes, with no limit
-- on presses.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day13.main < examples/2024/day13.txt
--
-- The proofs are in `Aoc.Year2024.Day13.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day13.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day13
import Std (Fail, IO, Int, List, Nat, Option, Parse, Text)
import Std.Parse (nat, newline, sections, text)

def main(): {IO, Fail} () :=
  let machines := parseMachines IO.readAll()
  IO.print "Part 1: ${solvePart1 machines}"
  IO.print "Part 2: ${solvePart2 machines}"

-- How far a button moves the claw, or how far the prize is from where the
-- claw starts.
type Offset = { x: Int, y: Int }

type Machine = { buttonA: Offset, buttonB: Offset, prize: Offset }

-- "X+94, Y+34" for a button, "X=8400, Y=5400" for the prize: `sign` is the
-- "+" or the "=".
def offset (sign: Text): {Parse} Offset :=
  text "X${sign}"
  let x := nat()
  text ", Y${sign}"
  let y := nat()
  { x = x.toInt, y = y.toInt }

-- Three lines: button A, button B and the prize.
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

-- Machines separated by blank lines.
def parseMachines (input: Text): {Fail} (List Machine) := Parse.all input (() => sections clawMachine)

-- What pressing A `aPresses` times and B `bPresses` times costs.
def tokens (aPresses: Nat) (bPresses: Nat): Nat := 3 * aPresses + bPresses

-- Whether those presses put the claw exactly over the prize.
def wins (machine: Machine) (aPresses: Nat) (bPresses: Nat): Bool :=
  aPresses.toInt * machine.buttonA.x + bPresses.toInt * machine.buttonB.x == machine.prize.x
    && aPresses.toInt * machine.buttonA.y + bPresses.toInt * machine.buttonB.y == machine.prize.y

-- 0 exactly when the buttons move the claw along the same line.
def determinant (machine: Machine): Int := machine.buttonA.x * machine.buttonB.y - machine.buttonA.y * machine.buttonB.x

-- Cramer's rule: with a nonzero determinant, the two equations have one
-- solution, and these are its presses if they are whole and not negative.
def onlyPresses (machine: Machine) (nonzero: determinant machine ≠ 0): Option (Nat, Nat) :=
  let prize := machine.prize
  let aPresses := (prize.x * machine.buttonB.y - prize.y * machine.buttonB.x) / determinant machine
  let bPresses := (machine.buttonA.x * prize.y - machine.buttonA.y * prize.x) / determinant machine
  Option.map2 (a b => (a, b)) aPresses.toNatChecked bPresses.toNatChecked |> .filter (((a, b)) => wins machine a b)

-- The fewest tokens over every press count up to `limit` for each button.
def searchTokens (limit: Nat) (machine: Machine): Option Nat :=
  List.range (limit + 1)
    |> .flatMap (aPresses =>
      List.range (limit + 1) |> .filter (bPresses => wins machine aPresses bPresses) |> .map (bPresses => tokens aPresses bPresses))
    |> .minimum

-- The fewest tokens that win with at most `limit` presses of each button.
-- Buttons along the same line may have many solutions, so they are searched.
def fewestTokensWithin (limit: Nat) (machine: Machine): Option Nat :=
  if nonzero: determinant machine ≠ 0 then
    onlyPresses machine nonzero
      |> .filter (((aPresses, bPresses)) => aPresses ≤ limit && bPresses ≤ limit)
      |> .map (((aPresses, bPresses)) => tokens aPresses bPresses)
  else searchTokens limit machine

-- How many presses of a button that moves the claw `step` move it exactly
-- `distance`, if some number does.
def pressesToCover (step: Offset) (distance: Offset): Option Nat :=
  let count := if step.x ≠ 0 then distance.x / step.x else if step.y ≠ 0 then distance.y / step.y else 0
  if count * step.x == distance.x && count * step.y == distance.y then count.toNatChecked else None

-- The prize's offset after `presses` of a button that moves the claw `step`.
def remaining (machine: Machine) (step: Offset) (presses: Nat): Offset :=
  { x = machine.prize.x - presses.toInt * step.x, y = machine.prize.y - presses.toInt * step.y }

-- The fewest tokens for buttons along the same line. Swapping presses of
-- one button for presses of the other that move the claw as far keeps a
-- win, so the cheapest win presses A fewer times than B moves along an
-- axis, or B fewer times than A does: try those counts.
def collinearTokens (machine: Machine): Option Nat :=
  let buttonA := machine.buttonA
  let buttonB := machine.buttonB
  let fewerA :=
    List.range (Nat.max buttonB.x.natAbs buttonB.y.natAbs + 1)
      |> .filterMap (aPresses => pressesToCover buttonB (remaining machine buttonA aPresses) |> .map (tokens aPresses))
  let fewerB :=
    List.range (Nat.max buttonA.x.natAbs buttonA.y.natAbs + 1)
      |> .filterMap (bPresses =>
        pressesToCover buttonA (remaining machine buttonB bPresses) |> .map (aPresses => tokens aPresses bPresses))
  (fewerA ++ fewerB).minimum

-- The fewest tokens that win, with no limit on presses.
def fewestTokens (machine: Machine): Option Nat :=
  if nonzero: determinant machine ≠ 0 then
    onlyPresses machine nonzero |> .map (((aPresses, bPresses)) => tokens aPresses bPresses)
  else collinearTokens machine

-- Part 2's prize, 10000000000000 further along both axes.
def corrected (machine: Machine): Machine :=
  let prize := machine.prize
  { machine | prize = { x = prize.x + 10000000000000, y = prize.y + 10000000000000 } }

def solvePart1 (machines: List Machine): Nat := machines.sumBy (machine => fewestTokensWithin 100 machine |> .getOrElse 0)

def solvePart2 (machines: List Machine): Nat := machines.sumBy (machine => corrected machine |> fewestTokens |> .getOrElse 0)
