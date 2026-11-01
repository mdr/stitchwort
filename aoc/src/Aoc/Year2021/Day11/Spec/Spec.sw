-- Day 11 as the puzzle states it, with no rounds: the octopuses that flash
-- in a step are the least set closed under "above 9 flashes", and the
-- answers are about runs of such steps. The grid is the program's
-- (`List (List Nat)`, row by row) and its cells std's `gridCells`; nothing
-- else is shared with the program. The proofs (Proofs/) show the program
-- computes these, for every grid.

namespace Aoc.Year2021.Day11.Spec
import Std (Exists, List, Nat)

-- Adjacent octopuses, "including diagonally": a different position at
-- most one row and at most one column away.
def adjacent (at: (Nat, Nat)) (other: (Nat, Nat)): Bool :=
  not (at.fst == other.fst && at.snd == other.snd)
    && at.fst ≤ other.fst + 1 && other.fst ≤ at.fst + 1 && at.snd ≤ other.snd + 1 && other.snd ≤ at.snd + 1

-- How many of the octopuses adjacent to `at` flash.
def flashingNeighbours (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool) (at: (Nat, Nat)): Nat :=
  levels.gridCells.count (((other, _)) => adjacent at other && flashed other)

-- An octopus's energy in a step in which `flashed` flash: its level goes
-- up by 1, and by 1 more for each adjacent octopus that flashes.
def energy (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool) (at: (Nat, Nat)) (level: Nat): Nat :=
  level + 1 + flashingNeighbours levels flashed at

-- "Any octopus with an energy level greater than 9 flashes": every
-- octopus whose energy, counting the flashes of `flashed`, is above 9 is
-- in `flashed`.
def Closed (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool): Prop :=
  (at: (Nat, Nat)) → (level: Nat) → (at, level) ∈ levels.gridCells → 9 < energy levels flashed at level → flashed at = True

-- The octopuses that flash in a step: the least closed set. Least, since
-- an octopus flashes only when the flashes before it push it above 9
-- (two adjacent 8s would each be above 9 if both flashed, but neither
-- starts the other off), and at most once.
def Flashers (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool): Prop :=
  Closed levels flashed ∧ ((other: (Nat, Nat) → Bool) → Closed levels other → (at: (Nat, Nat)) → flashed at = True → other at = True)

-- The levels after the step: "any octopus that flashed during this step
-- has its energy level set to 0", the others are at their energy.
def after (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool): List (List Nat) :=
  levels.mapWithIndex (r row => row.mapWithIndex (c level => if flashed (r, c) then 0 else energy levels flashed (r, c) level))

-- The number of octopuses that flash.
def flashCount (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool): Nat := levels.gridCells.count (((at, _)) => flashed at)

-- `steps` steps take `levels` to `final`, with `total` flashes in all.
type Run: List (List Nat) → Nat → List (List Nat) → Nat → Prop =
  | Start (levels: List (List Nat)): Run levels 0 levels 0
  | Step (flashed: (Nat, Nat) → Bool) (flashers: Flashers levels flashed) (rest: Run (after levels flashed) steps final total):
    Run levels (Succ steps) final (flashCount levels flashed + total)

-- Part 1: "how many total flashes are there after 100 steps?"
def Part1Answer (levels: List (List Nat)) (answer: Nat): Prop := exists (final: List (List Nat)) => Run levels 100 final answer

-- In step `number` (counting from 1) every octopus flashes.
def AllFlashIn (levels: List (List Nat)) (number: Nat): Prop :=
  1 ≤ number
    ∧ exists (before: List (List Nat)) => exists (total: Nat) => Run levels (number - 1) before total
      ∧ exists (flashed: (Nat, Nat) → Bool) => Flashers before flashed
        ∧ ((at: (Nat, Nat)) → (level: Nat) → (at, level) ∈ before.gridCells → flashed at = True)

-- Part 2: "the first step during which all octopuses flash".
def Part2Answer (levels: List (List Nat)) (answer: Nat): Prop :=
  AllFlashIn levels answer ∧ ((earlier: Nat) → earlier < answer → Not (AllFlashIn levels earlier))
