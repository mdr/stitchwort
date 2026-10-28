-- Day 18 as the puzzle states it, over the program's positions and their
-- neighbours in each direction (`step`), with the corrupted positions a
-- list of the bytes fallen so far. The proofs (Proofs/) show the program's
-- answers are these, for every size and list of bytes.

namespace Aoc.Year2024.Day18.Spec
import Aoc.Year2024.Day18 (..)
import Std (And, Bool, Exists, List, Nat, Option)

-- "Your memory space is a two-dimensional grid with coordinates that range
-- from 0 to 70 both horizontally and vertically" (0 to `size - 1` here).
-- "Corrupted memory coordinates cannot be entered by you or The
-- Historians".
def isSafe (size: Nat) (fallen: List Position) (position: Position): Bool :=
  position.x < size && position.y < size && !fallen.contains position

-- "You can step up, down, left, or right": the position one step from
-- `position`; `None` if the step leaves the memory space or enters a
-- corrupted position.
def stepTo (size: Nat) (fallen: List Position) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if isSafe size fallen next then Some next else None
    | None => None

-- Where some steps from `position` end; `None` if one can't be taken.
def walk (size: Nat) (fallen: List Position) (position: Position): List Direction → Option Position
  | Nil => Some position
  | Cons direction rest =>
    match stepTo size fallen position direction with
      | Some next => walk size fallen next rest
      | None => None

-- "You and The Historians are currently in the top left corner of the
-- memory space (at 0,0) and need to reach the exit in the bottom right
-- corner": steps from a safe start that end at the exit.
def IsPath (size: Nat) (fallen: List Position) (steps: List Direction): Prop :=
  And (isSafe size fallen Position.start = True) (walk size fallen Position.start steps = Some ({ x = size - 1, y = size - 1 }: Position))

-- "what is the minimum number of steps needed to reach the exit?": some
-- path takes `fewest` steps, and none takes fewer.
def IsFewestSteps (size: Nat) (fallen: List Position) (fewest: Nat): Prop :=
  And (Exists (List Direction) (steps => And (IsPath size fallen steps) (steps.length = fewest)))
    ((steps: List Direction) → IsPath size fallen steps → fewest ≤ steps.length)

-- The exit can be reached once the first `count` bytes have fallen.
def HasPath (size: Nat) (bytes: List Position) (count: Nat): Prop := Exists (List Direction) (steps => IsPath size (bytes.take count) steps)

-- "What are the coordinates of the first byte that will prevent the exit
-- from being reachable from your starting position?": the byte at some
-- index, with no path once it has fallen and a path before any byte up to
-- it has.
def IsFirstBlocking (size: Nat) (bytes: List Position) (byte: Position): Prop :=
  Exists Nat (index =>
    And (bytes.get index = Some byte)
      (And (Not (HasPath size bytes (index + 1))) ((earlier: Nat) → earlier ≤ index → HasPath size bytes earlier)))
