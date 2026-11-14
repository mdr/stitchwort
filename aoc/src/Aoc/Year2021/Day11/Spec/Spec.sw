--| Day 11 as the puzzle states it, with no rounds: the octopuses that flash
--| in a step are the least set closed under "above 9 flashes", and the
--| answers are about runs of such steps. The cavern is the program's
--| (`Cavern`, a grid of levels), and its cells (`Grid.cells`, `Grid.map`)
--| and adjacency (`touching`) the shared grid code's; nothing else is
--| shared with the program. The proofs (Proofs/) show the program computes
--| these, for every grid.

namespace Aoc.Year2021.Day11.Spec
import Aoc.Year2021.Day11 (Cavern)
import Aoc.Common (Position, touching)
import Std (Exists, Nat)

--| Adjacent octopuses, "including diagonally": a different position at
--| most one row and at most one column away, the shared grid code's
--| `touching`.

--| How many of the octopuses adjacent to `at` flash.
def flashingNeighbours (cavern: Cavern) (flashed: Position → Bool) (at: Position): Nat :=
  cavern.grid.cells.count (((other, _)) => touching at other && flashed other)

--| An octopus's energy in a step in which `flashed` flash: its level goes
--| up by 1, and by 1 more for each adjacent octopus that flashes.
def energyIn (cavern: Cavern) (flashed: Position → Bool) (at: Position) (level: Nat): Nat :=
  level + 1 + flashingNeighbours cavern flashed at

--| "Any octopus with an energy level greater than 9 flashes": every
--| octopus whose energy, counting the flashes of `flashed`, is above 9 is
--| in `flashed`.
def Closed (cavern: Cavern) (flashed: Position → Bool): Prop :=
  ∀ (at: Position) (level: Nat) => (at, level) ∈ cavern.grid.cells
    → 9 < energyIn cavern flashed at level
    → flashed at = True

--| The octopuses that flash in a step: the least closed set. Least, since
--| an octopus flashes only when the flashes before it push it above 9
--| (two adjacent 8s would each be above 9 if both flashed, but neither
--| starts the other off), and at most once.
def Flashers (cavern: Cavern) (flashed: Position → Bool): Prop :=
  Closed cavern flashed
    ∧ (∀ (other: Position → Bool) => Closed cavern other → ∀ (at: Position) => flashed at = True → other at = True)

--| The cavern after the step: "any octopus that flashed during this step
--| has its energy level set to 0", the others are at their energy.
def after (cavern: Cavern) (flashed: Position → Bool): Cavern :=
  { grid = cavern.grid.map (at level => if flashed at then 0 else energyIn cavern flashed at level) }

--| The number of octopuses that flash.
def flashCount (cavern: Cavern) (flashed: Position → Bool): Nat := cavern.grid.cells.count (((at, _)) => flashed at)

--| `steps` steps take `cavern` to `final`, with `total` flashes in all.
type Run: Cavern → Nat → Cavern → Nat → Prop =
  | Start (cavern: Cavern): Run cavern 0 cavern 0
  | Step
      (flashed: Position → Bool)
      (flashers: Flashers cavern flashed)
      (rest: Run (after cavern flashed) steps final total): Run cavern
    (Succ steps)
    final
    (flashCount cavern flashed + total)

--| Part 1: "how many total flashes are there after 100 steps?"
def Part1Answer (cavern: Cavern) (answer: Nat): Prop := exists (final: Cavern) => Run cavern 100 final answer

--| In step `number` (counting from 1) every octopus flashes.
def AllFlashIn (cavern: Cavern) (number: Nat): Prop :=
  1 ≤ number
    ∧ exists (before: Cavern) => exists (total: Nat) => Run cavern (number - 1) before total
      ∧ exists (flashed: Position → Bool) => Flashers before flashed
        ∧ (∀ (at: Position) (level: Nat) => (at, level) ∈ before.grid.cells → flashed at = True)

--| Part 2: "the first step during which all octopuses flash".
def Part2Answer (cavern: Cavern) (answer: Nat): Prop :=
  AllFlashIn cavern answer ∧ (∀ (earlier: Nat) => earlier < answer → ¬(AllFlashIn cavern earlier))
