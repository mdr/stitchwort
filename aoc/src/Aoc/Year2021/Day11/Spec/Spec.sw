--| Day 11 as the puzzle states it, with no rounds: the octopuses that flash
--| in a step are the least set closed under "above 9 flashes", and the
--| answers are about runs of such steps. The grid is the program's
--| (`List (List Nat)`, row by row), and its positions and cells (`cells`)
--| and adjacency (`touching`) the shared grid code's; nothing else is
--| shared with the program. The proofs (Proofs/) show the program computes
--| these, for every grid.

namespace Aoc.Year2021.Day11.Spec
import Aoc.Common (Position, cells, touching)
import Std (Exists, List, Nat)

--| Adjacent octopuses, "including diagonally": a different position at
--| most one row and at most one column away, the shared grid code's
--| `touching`.

--| How many of the octopuses adjacent to `at` flash.
def flashingNeighbours (levels: List (List Nat)) (flashed: Position → Bool) (at: Position): Nat :=
  (cells levels).count (((other, _)) => touching at other && flashed other)

--| An octopus's energy in a step in which `flashed` flash: its level goes
--| up by 1, and by 1 more for each adjacent octopus that flashes.
def energyIn (levels: List (List Nat)) (flashed: Position → Bool) (at: Position) (level: Nat): Nat :=
  level + 1 + flashingNeighbours levels flashed at

--| "Any octopus with an energy level greater than 9 flashes": every
--| octopus whose energy, counting the flashes of `flashed`, is above 9 is
--| in `flashed`.
def Closed (levels: List (List Nat)) (flashed: Position → Bool): Prop :=
  (at: Position) → (level: Nat) → (at, level) ∈ cells levels → 9 < energyIn levels flashed at level → flashed at = True

--| The octopuses that flash in a step: the least closed set. Least, since
--| an octopus flashes only when the flashes before it push it above 9
--| (two adjacent 8s would each be above 9 if both flashed, but neither
--| starts the other off), and at most once.
def Flashers (levels: List (List Nat)) (flashed: Position → Bool): Prop :=
  Closed levels flashed ∧ ((other: Position → Bool) → Closed levels other → (at: Position) → flashed at = True → other at = True)

--| The levels after the step: "any octopus that flashed during this step
--| has its energy level set to 0", the others are at their energy.
def after (levels: List (List Nat)) (flashed: Position → Bool): List (List Nat) :=
  levels.mapWithIndex (r row => row.mapWithIndex (c level => if flashed { row = r, column = c } then 0 else energyIn levels flashed { row = r, column = c } level))

--| The number of octopuses that flash.
def flashCount (levels: List (List Nat)) (flashed: Position → Bool): Nat := (cells levels).count (((at, _)) => flashed at)

--| `steps` steps take `levels` to `final`, with `total` flashes in all.
type Run: List (List Nat) → Nat → List (List Nat) → Nat → Prop =
  | Start (levels: List (List Nat)): Run levels 0 levels 0
  | Step (flashed: Position → Bool) (flashers: Flashers levels flashed) (rest: Run (after levels flashed) steps final total):
    Run levels (Succ steps) final (flashCount levels flashed + total)

--| Part 1: "how many total flashes are there after 100 steps?"
def Part1Answer (levels: List (List Nat)) (answer: Nat): Prop := exists (final: List (List Nat)) => Run levels 100 final answer

--| In step `number` (counting from 1) every octopus flashes.
def AllFlashIn (levels: List (List Nat)) (number: Nat): Prop :=
  1 ≤ number
    ∧ exists (before: List (List Nat)) => exists (total: Nat) => Run levels (number - 1) before total
      ∧ exists (flashed: Position → Bool) => Flashers before flashed
        ∧ ((at: Position) → (level: Nat) → (at, level) ∈ cells before → flashed at = True)

--| Part 2: "the first step during which all octopuses flash".
def Part2Answer (levels: List (List Nat)) (answer: Nat): Prop :=
  AllFlashIn levels answer ∧ ((earlier: Nat) → earlier < answer → ¬(AllFlashIn levels earlier))
