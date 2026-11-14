--| Day 12 as the puzzle states it, about the instructions (the program's
--| `Instruction`, an action and a value) and places (the program's
--| `Location`, `x` east and `y` north of the start): how each instruction is
--| written, what it does to the ship in each part, and the answer. Which
--| way the ship faces is a step east or north, here, not a compass point,
--| and a turn is turning that step; nothing else is shared with the
--| program. The proofs (Proofs/) show the program computes these.

namespace Aoc.Year2020.Day12.Spec
import Aoc.Common (Heading)
import Aoc.Year2020.Day12 (Action, Instruction, Location, Side)
import Std (Char, Int, List, Nat, Parse)

-- The format

def ActionWritten (letter: Char) (action: Action): Prop := match action with
  | Move North => letter = 'N'
  | Move South => letter = 'S'
  | Move East => letter = 'E'
  | Move West => letter = 'W'
  | Turn Left => letter = 'L'
  | Turn Right => letter = 'R'
  | Forward => letter = 'F'

--| "Each instruction consists of a single-character action paired with an
--| integer input value": the letter, then the value in decimal. The ship
--| only ever faces north, south, east or west, so a turn is by a multiple
--| of 90 degrees (every one in the examples and the input is 90, 180 or
--| 270).
def InstructionWritten (read: List Char) (instruction: Instruction): Prop :=
  ∃ (letter: Char) => ∃ (digits: List Char) => read = [letter, ..digits]
    ∧ ActionWritten letter instruction.action
    ∧ digits ≠ []
    ∧ digits.all Parse.isDigit = True
    ∧ instruction.value = Parse.digitsValue digits
    ∧ (instruction.action.isTurn = True → instruction.value % 90 = 0)

-- Moving and turning

--| A step of one unit north, south, east or west.
def unit: Heading → Location
  | North => { x = 0, y = 1 }
  | South => { x = 0, y = -1 }
  | East => { x = 1, y = 0 }
  | West => { x = -1, y = 0 }

--| `distance` steps of `step` on from `location`.
def along (location step: Location) (distance: Nat): Location :=
  { x = location.x + distance.toInt * step.x, y = location.y + distance.toInt * step.y }

--| A quarter turn left (counter-clockwise) about the start: east becomes
--| north, and north becomes west.
def quarterLeft (location: Location): Location := { x = 0 - location.y, y = location.x }

--| A quarter turn right (clockwise): east becomes south.
def quarterRight (location: Location): Location := { x = location.y, y = 0 - location.x }

--| Turned `degrees` to `side`, a multiple of 90 (InstructionWritten): that
--| many quarter turns.
def turned (side: Side) (degrees: Nat) (location: Location): Location := match side with
  | Left => Nat.iterate (degrees / 90) quarterLeft location
  | Right => Nat.iterate (degrees / 90) quarterRight location

--| "The Manhattan distance between that location and the ship's starting
--| position": "the sum of the absolute values of its east/west position and
--| its north/south position".
def manhattan (location: Location): Nat := location.x.natAbs + location.y.natAbs

-- Part 1

--| The ship, and the step it would take forward.
type Ship = { position: Location, facing: Location }

--| "The ship starts by facing east."
def start: Ship := { position = { x = 0, y = 0 }, facing = unit East }

--| "Action N means to move north by the given value", and S, E and W
--| likewise; "Action L means to turn left the given number of degrees", and
--| R right; "Action F means to move forward by the given value in the
--| direction the ship is currently facing."
def navigate (ship: Ship) (instruction: Instruction): Ship := match instruction.action with
  | Move heading => { ship | position = along ship.position (unit heading) instruction.value }
  | Turn side => { ship | facing = turned side instruction.value ship.facing }
  | Forward => { ship | position = along ship.position ship.facing instruction.value }

--| "Figure out where the navigation instructions lead. What is the
--| Manhattan distance between that location and the ship's starting
--| position?"
def Part1 (instructions: List Instruction) (answer: Nat): Prop :=
  answer = manhattan (instructions.foldLeft start navigate).position

-- Part 2

--| The ship, and the waypoint, "relative to the ship".
type Steered = { position: Location, waypoint: Location }

--| "The waypoint starts 10 units east and 1 unit north relative to the
--| ship."
def steeredStart: Steered := { position = { x = 0, y = 0 }, waypoint = { x = 10, y = 1 } }

--| "Action N means to move the waypoint north by the given value", and S,
--| E and W likewise; "Action L means to rotate the waypoint around the ship
--| left (counter-clockwise) the given number of degrees", and R right
--| (clockwise); "Action F means to move forward to the waypoint a number of
--| times equal to the given value." The waypoint moves with the ship.
def steer (ship: Steered) (instruction: Instruction): Steered := match instruction.action with
  | Move heading => { ship | waypoint = along ship.waypoint (unit heading) instruction.value }
  | Turn side => { ship | waypoint = turned side instruction.value ship.waypoint }
  | Forward => { ship | position = along ship.position ship.waypoint instruction.value }

--| "What is the Manhattan distance between that location and the ship's
--| starting position?"
def Part2 (instructions: List Instruction) (answer: Nat): Prop :=
  answer = manhattan (instructions.foldLeft steeredStart steer).position
