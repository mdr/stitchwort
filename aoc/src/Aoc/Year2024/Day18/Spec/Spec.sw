--| Day 18 as the puzzle states it, over the shared grid code's positions,
--| with the corrupted positions a list of the bytes fallen so far. The
--| puzzle's coordinates are X, the distance from the left edge, and Y, from
--| the top edge: X is a position's column and Y its row. The proofs
--| (Proofs/) show the program's answers are these, for every size and list
--| of bytes.

namespace Aoc.Year2024.Day18.Spec
import Aoc.Year2024.Day18 (..)
import Aoc.Common (Position, isPath)
import Std (And, Bool, Exists, List, Nat, Option)

--| "Your memory space is a two-dimensional grid with coordinates that range
--| from 0 to 70 both horizontally and vertically" (0 to `size - 1` here, in
--| each of the first `size` rows and columns). "Corrupted memory
--| coordinates cannot be entered by you or The Historians".
def isSafe (size: Nat) (fallen: List Position) (position: Position): Bool :=
  position.within size size && !fallen.contains position

--| "You and The Historians are currently in the top left corner of the
--| memory space (at 0,0) and need to reach the exit in the bottom right
--| corner (at 70,70)". "You can step up, down, left, or right": a path is
--| the positions entered in turn, each next to the one before (the shared
--| grid code's `isPath`: up, down, left or right) and safe, from a safe
--| start to the exit. Each position entered is a step.
def IsPath (size: Nat) (fallen steps: List Position): Prop :=
  (isSafe size fallen { row = 0, column = 0 } = True)
    ∧ (isPath (isSafe size fallen) { row = 0, column = 0 } steps { row = size - 1, column = size - 1 } = True)

--| "what is the minimum number of steps needed to reach the exit?": some
--| path takes `fewest` steps, and none takes fewer.
def IsFewestSteps (size: Nat) (fallen: List Position) (fewest: Nat): Prop :=
  (Exists (List Position) (steps => (IsPath size fallen steps) ∧ (steps.length = fewest)))
    ∧ (∀ (steps: List Position) => IsPath size fallen steps → fewest ≤ steps.length)

--| The exit can be reached once the first `count` bytes have fallen.
def HasPath (size: Nat) (bytes: List Position) (count: Nat): Prop :=
  Exists (List Position) (steps => IsPath size (bytes.take count) steps)

--| "What are the coordinates of the first byte that will prevent the exit
--| from being reachable from your starting position?": the byte at some
--| index, with no path once it has fallen and a path before any byte up to
--| it has.
def IsFirstBlocking (size: Nat) (bytes: List Position) (byte: Position): Prop := Exists Nat (index =>
  (bytes.get index = Some byte)
    ∧ ((¬(HasPath size bytes (index + 1))) ∧ (∀ (earlier: Nat) => earlier ≤ index → HasPath size bytes earlier)))
