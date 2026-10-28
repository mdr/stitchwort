-- Advent of Code 2024, day 21: door codes to type on a numeric keypad, whose
-- robot is driven from a directional keypad, whose robot is driven from
-- another, and so on up to the directional keypad you press yourself. A
-- code's complexity is the fewest presses you need to type it times its
-- numeric part. Part 1 adds up the complexities with two robots on
-- directional keypads between you and the door; part 2 with 25.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day21.main < examples/2024/day21.txt
--
-- The proofs are in `Aoc.Year2024.Day21.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day21.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day21
import Std (Fail, IO, List, Nat, Option, Parse, Text)
import Std.Parse (label, lines, many1, pick)

def main(): {IO, Fail} () :=
  let codes := parseCodes IO.readAll()
  IO.print "Part 1: ${solvePart1 codes}"
  IO.print "Part 2: ${solvePart2 codes}"

type Direction =
  | Up
  | Down
  | Left
  | Right

-- A key on a directional keypad: an arrow moves the arm it drives, and A
-- presses the key that arm aims at.
type DirectionKey =
  | Arrow (direction: Direction)
  | Activate

-- A key on the door's numeric keypad.
type NumericKey =
  | Digit0
  | Digit1
  | Digit2
  | Digit3
  | Digit4
  | Digit5
  | Digit6
  | Digit7
  | Digit8
  | Digit9
  | Enter

type Code = List NumericKey

def numericKey(): {Parse} NumericKey :=
  label "a key (0 to 9 or A)" (() =>
    pick [
      ("0", Digit0),
      ("1", Digit1),
      ("2", Digit2),
      ("3", Digit3),
      ("4", Digit4),
      ("5", Digit5),
      ("6", Digit6),
      ("7", Digit7),
      ("8", Digit8),
      ("9", Digit9),
      ("A", Enter)
    ])

-- One code per line.
def codes(): {Parse} (List Code) := lines (() => many1 numericKey)

def parseCodes (input: Text): {Fail} (List Code) := Parse.all input codes

-- The digit on a key, if it has one.
def NumericKey.digit (key: NumericKey): Option Nat :=
  match key with
    | Digit0 => Some 0
    | Digit1 => Some 1
    | Digit2 => Some 2
    | Digit3 => Some 3
    | Digit4 => Some 4
    | Digit5 => Some 5
    | Digit6 => Some 6
    | Digit7 => Some 7
    | Digit8 => Some 8
    | Digit9 => Some 9
    | Enter => None

-- The code's digits read as a number: 29 for 029A.
def Code.numericPart (code: Code): Nat := code.foldLeft 0 (number key => key.digit.fold number (digit => 10 * number + digit))

type Position = { row: Nat, column: Nat }

-- Where a keypad's keys are, and its gap, which is in a corner.
type Keypad (k: Type) = { place: k → Position, gap: Position }

--     +---+---+
--     | ^ | A |
-- +---+---+---+
-- | < | v | > |
-- +---+---+---+
def Keypad.directional: Keypad DirectionKey := {
  place = key =>
    match key with
      | Arrow Up => { row = 0, column = 1 }
      | Activate => { row = 0, column = 2 }
      | Arrow Left => { row = 1, column = 0 }
      | Arrow Down => { row = 1, column = 1 }
      | Arrow Right => { row = 1, column = 2 },
  gap = { row = 0, column = 0 }
}

-- +---+---+---+
-- | 7 | 8 | 9 |
-- +---+---+---+
-- | 4 | 5 | 6 |
-- +---+---+---+
-- | 1 | 2 | 3 |
-- +---+---+---+
--     | 0 | A |
--     +---+---+
def Keypad.numeric: Keypad NumericKey := {
  place = key =>
    match key with
      | Digit7 => { row = 0, column = 0 }
      | Digit8 => { row = 0, column = 1 }
      | Digit9 => { row = 0, column = 2 }
      | Digit4 => { row = 1, column = 0 }
      | Digit5 => { row = 1, column = 1 }
      | Digit6 => { row = 1, column = 2 }
      | Digit1 => { row = 2, column = 0 }
      | Digit2 => { row = 2, column = 1 }
      | Digit3 => { row = 2, column = 2 }
      | Digit0 => { row = 3, column = 1 }
      | Enter => { row = 3, column = 2 },
  gap = { row = 3, column = 0 }
}

-- `count` moves one way.
def steps (count: Nat) (direction: Direction): List Direction := List.replicate count direction

-- The moves along a row, then along a column, from one place to another.
def acrossThenAlong (from: Position) (to: Position): List Direction :=
  let across := if to.column < from.column then steps (from.column - to.column) Left else steps (to.column - from.column) Right
  let along := if to.row < from.row then steps (from.row - to.row) Up else steps (to.row - from.row) Down
  List.append across along

-- The moves along a column, then along a row.
def alongThenAcross (from: Position) (to: Position): List Direction :=
  let along := if to.row < from.row then steps (from.row - to.row) Up else steps (to.row - from.row) Down
  let across := if to.column < from.column then steps (from.column - to.column) Left else steps (to.column - from.column) Right
  List.append along across

-- The ways to move the arm between two keys: all the moves across, then
-- all along, or the other way round. The gap is in a corner, so a way
-- passes over it only if it turns there; those are left out.
def Keypad.routes (keypad: Keypad k) (from: k) (to: k): List (List Direction) :=
  let start := keypad.place from
  let end := keypad.place to
  let acrossTurn: Position := { row = start.row, column = end.column }
  let alongTurn: Position := { row = end.row, column = start.column }
  List.append
    (if acrossTurn == keypad.gap then [] else [acrossThenAlong start end])
    (if alongTurn == keypad.gap then [] else [alongThenAcross start end])

-- How many of your presses it takes to press `to` on some keypad whose arm
-- aims at `from`, with every keypad between yours and it aiming at A.
type Costs = DirectionKey → DirectionKey → Nat

-- On your own keypad, one press.
def Costs.yours: Costs := from to => 1

-- Your presses to press `keys` in turn on a keypad whose arm aims at A.
def Costs.sequenceCost (costs: Costs) (keys: List DirectionKey): Nat :=
  Cons Activate keys |> .zipWithNext |> .sumBy (((from, to)) => costs from to)

-- The keys to press on the driving keypad to take a route and press the
-- key at its end.
def routeKeys (route: List Direction): List DirectionKey := List.append (route.map Arrow) [Activate]

-- Your presses to take a route and press the key at its end.
def Costs.routeCost (costs: Costs) (route: List Direction): Nat := costs.sequenceCost (routeKeys route)

-- The route costing the fewest of your presses.
def Costs.cheapestRoute (costs: Costs) (choices: List (List Direction)): List Direction := choices.minBy costs.routeCost |> .getOrElse []

-- What the cheapest route costs.
def Costs.cheapestCost (costs: Costs) (choices: List (List Direction)): Nat := costs.routeCost (costs.cheapestRoute choices)

def directionKeys: List DirectionKey := [Arrow Up, Arrow Down, Arrow Left, Arrow Right, Activate]

def DirectionKey.index (key: DirectionKey): Nat :=
  match key with
    | Arrow Up => 0
    | Arrow Down => 1
    | Arrow Left => 2
    | Arrow Right => 3
    | Activate => 4

-- The same costs, worked out once for every pair of keys.
def Costs.tabulate (costs: Costs): Costs :=
  let table := directionKeys.map (from => directionKeys.map (to => costs from to))
  from to => table.getOr from.index [] |> .getOr to.index 0

-- The costs one keypad further from yours: the cheapest route on that
-- keypad, typed on the one before it.
def Costs.next (costs: Costs): Costs :=
  Costs.tabulate (from to => costs.cheapestCost (Keypad.directional.routes from to))

-- The costs on the directional keypad that drives the door's robot, with
-- `robots` robots on directional keypads.
def robotCosts (robots: Nat): Costs := Nat.iterate robots Costs.next Costs.yours

-- The fewest presses you need for the door's robot to type `code`.
def Costs.shortestLength (costs: Costs) (code: Code): Nat :=
  Cons Enter code
    |> .zipWithNext
    |> .sumBy (((from, to)) => costs.cheapestCost (Keypad.numeric.routes from to))

-- The sum of the codes' complexities with `robots` robots on directional
-- keypads.
def complexities (robots: Nat) (codes: List Code): Nat :=
  let costs := robotCosts robots
  codes.sumBy (code => costs.shortestLength code * code.numericPart)

def solvePart1 (codes: List Code): Nat := complexities 2 codes

def solvePart2 (codes: List Code): Nat := complexities 25 codes
