-- Day 21 as the puzzle states it: the keypads as their rows of keys, each
-- robot's arm moved by arrows and pressing with A, never aimed at a gap,
-- and your presses passed down the chain of keypads to the door. A press
-- sequence types a code if the door's keypad gets exactly the code's keys;
-- the shortest length is the least length of such a sequence. The proofs
-- (Proofs/) show the program's length is achieved by a sequence that types
-- the code, for every code and number of robots; that no shorter sequence
-- exists is proved only with no robots on directional keypads.

namespace Aoc.Year2024.Day21.Spec
import Aoc.Year2024.Day21 (..)
import Std (And, Exists, List, Nat, Option)

-- "a gap / ^ (up) / A (activate) on the first row and < (left) / v
-- (down) / > (right) on the second row".
def directionalRows: List (List (Option DirectionKey)) := [
  [None, Some (Arrow Up), Some Activate],
  [Some (Arrow Left), Some (Arrow Down), Some (Arrow Right)]
]

-- "four rows of buttons: 789, 456, 123, and finally an empty gap followed
-- by 0A".
def numericRows: List (List (Option NumericKey)) := [
  [Some Digit7, Some Digit8, Some Digit9],
  [Some Digit4, Some Digit5, Some Digit6],
  [Some Digit1, Some Digit2, Some Digit3],
  [None, Some Digit0, Some Enter]
]

-- "All robots will initially aim at the keypad's A key, wherever it is".
def directionalStart: Position := { row = 0, column = 2 }

def numericStart: Position := { row = 3, column = 2 }

-- The key an arm aims at: none at a gap or off the keypad.
def keyAt (rows: List (List (Option k))) (aim: Position): Option k := rows.getOr aim.row [] |> .getOr aim.column None

-- "the up / down / left / right buttons cause it to move its arm one
-- button in that direction"; none off the top or the left.
def moved (aim: Position) (direction: Direction): Option Position :=
  match direction with
    | Up => if aim.row == 0 then None else Some ({ aim | row = aim.row - 1 })
    | Down => Some ({ aim | row = aim.row + 1 })
    | Left => if aim.column == 0 then None else Some ({ aim | column = aim.column - 1 })
    | Right => Some ({ aim | column = aim.column + 1 })

-- The keys a robot presses when driven by `presses`, its arm at `aim`:
-- "the A button causes the robot to briefly move forward, pressing the
-- button being aimed at by the robotic arm". None if the arm is ever aimed
-- at a gap ("the robot will panic unrecoverably") or off the keypad.
def operate (rows: List (List (Option k))) (aim: Position): List DirectionKey → Option (List k)
  | Nil => Some Nil
  | Cons Activate rest => keyAt rows aim |> .flatMap (key => operate rows aim rest |> .map (Cons key))
  | Cons (Arrow direction) rest =>
    moved aim direction |> .flatMap (next => keyAt rows next |> .flatMap (key => operate rows next rest))

-- The keys typed on the door when you press `presses`, with `robots`
-- robots on directional keypads between: "your directional keypad
-- controls a robot which is typing on a directional keypad which controls a
-- robot which is typing on a directional keypad... and so on, ending with
-- the robot which is typing on the numeric keypad".
def typed (robots: Nat) (presses: List DirectionKey): Option Code :=
  match robots with
    | Zero => operate numericRows numericStart presses
    | Succ others => operate directionalRows directionalStart presses |> .flatMap (typed others)

-- `presses` "cause the desired code to be typed on the numeric keypad".
def Types (robots: Nat) (code: Code) (presses: List DirectionKey): Prop := typed robots presses = Some code

-- "the length of the shortest sequence of button presses you need to type
-- on your directional keypad in order to cause the code to be typed": some
-- sequence of that length types the code, and none shorter does.
def Shortest (robots: Nat) (code: Code) (length: Nat): Prop :=
  And
    (Exists (List DirectionKey) (presses => And (Types robots code presses) (presses.length = length)))
    ((presses: List DirectionKey) → Types robots code presses → length ≤ presses.length)

-- "The complexity of a single code ... the result of multiplying these two
-- values", summed over the codes, given each code's shortest length. The
-- numeric part ("ignoring leading zeroes") is the program's
-- `Code.numericPart`.
def complexitySum (codes: List Code) (shortest: Code → Nat): Nat := codes.sumBy (code => shortest code * Code.numericPart code)

-- "What is the sum of the complexities of the five codes on your list?",
-- with `robots` robots on directional keypads: two in part 1, 25 in part 2.
def Answer (robots: Nat) (codes: List Code) (answer: Nat): Prop :=
  Exists (Code → Nat) (shortest =>
    And ((code: Code) → code ∈ codes → Shortest robots code (shortest code)) (answer = complexitySum codes shortest))
