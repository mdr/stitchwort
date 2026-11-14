--| Advent of Code 2021, day 11: a grid of octopuses, each with an energy
--| level from 0 to 9. In a step every level goes up by 1; then each octopus
--| above 9 flashes, giving 1 more to each of the eight around it (diagonals
--| too), which can make them flash in turn; no octopus flashes twice in a
--| step, and every one that flashed ends the step at 0. Part 1 counts the
--| flashes in 100 steps; part 2 finds the first step in which every octopus
--| flashes.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2021.Day11.main < inputs/2021/day11.txt
--|
--| The puzzle input is committed in aoc/inputs/2021/.
--|
--| A step works out who flashes in rounds: an octopus flashes once its
--| level, plus 1, plus the flashers around it so far, is above 9, and the
--| rounds go on until one adds nobody. The proofs that this is the puzzle's
--| step (the least set of flashers), and that both answers are the
--| puzzle's, are in `Aoc.Year2021.Day11.Proofs` (Proofs/); the tests in
--| `Aoc.Year2021.Day11.Tests` (Tests/). `run` checks neither.

namespace Aoc.Year2021.Day11
import Aoc.Common (Grid, Position, firstWidth, parseGrid)
import Std (Bool, Fail, Fin, IO, List, Nat, Option, Parse, Text)
import Std.Parse (digit)

--| The cavern: a grid of octopuses, each with its energy level.
type Cavern = { grid: Grid Nat }

--| The octopuses that have flashed so far in a step, one flag per octopus
--| of the cavern.
type Flashed = { grid: Grid Bool }

def main(): {IO, Fail} () :=
  let cavern := parseCavern IO.readAll()
  IO.print "Part 1: ${cavern.solvePart1}"
  IO.print "Part 2: ${cavern.solvePart2 |> .orFail "no step within ${syncLimit} has every octopus flash"}"

--| One row of digits per line, every row as long as the first.
def parseCavern (input: Text): {Fail} Cavern := Cavern.ofDigits (parseGrid input digit)

--| The digits as energy levels.
def Cavern.ofDigits (digits: Grid (Fin 10)): Cavern := {
  grid = {
    rows = digits.rows.map (row => row.map Fin.toNat),
    nonEmpty = rewrite digitsFirstWidth digits.rows in digits.nonEmpty
  }
}

--| Reading the digits as numbers keeps the first row's length (so the
--| cavern has a first row with an octopus).
theorem digitsFirstWidth ∀ (rows: List (List (Fin 10))):
    firstWidth (rows.map (digits => digits.map Fin.toNat)) = firstWidth rows :=
  match rows with
    | [] => rfl
    | [first, ..rest] => List.lengthMap first Fin.toNat

--| The octopuses with their positions and levels, row by row.
def Cavern.cells (cavern: Cavern): List (Position, Nat) := cavern.grid.cells

--| `f` of every octopus's position and level, in a cavern of the same shape.
def Cavern.map (cavern: Cavern) (f: Position → Nat → Nat): Cavern := { grid = cavern.grid.map f }

--| Whether the octopus at `at` has flashed (none off the cavern has).
def Flashed.has (flashed: Flashed) (at: Position): Bool := flashed.grid.at at |> .getOrElse False

--| Whether each octopus has flashed, as `flashes` says from its position and level.
def Cavern.flash (cavern: Cavern) (flashes: Position → Nat → Bool): Flashed := { grid = cavern.grid.map flashes }

--| The flashers of a cavern before any round: nobody.
def Cavern.noFlashers (cavern: Cavern): Flashed := cavern.flash (_ _ => False)

--| The level of the octopus at `at` in this step: its level before, plus
--| 1, plus 1 for each octopus around it that has flashed.
def Flashed.energy (flashed: Flashed) (at: Position) (level: Nat): Nat := level + 1 + at.around.count flashed.has

--| `Flashed.has`, through a table built once (`Grid.lookupOr`): O(1) per
--| octopus where `has` walks the rows. Partly applied, `flashed.lookup`
--| builds the table once for a whole round or step.
def Flashed.lookup (flashed: Flashed): Position → Bool := flashed.grid.lookupOr False

--| `Flashed.energy`, from the flashers' table `has` (`flashed.lookup`) and
--| without building the positions around as lists
--| (`Aoc.Year2021.Day11.Proofs.energyWithIsEnergy`).
def energyWith (has: Position → Bool) (at: Position) (level: Nat): Nat := level + 1 + at.countAround has

--| One round: an octopus flashes if its energy, given those that have
--| flashed so far, is above 9. (`Aoc.Year2021.Day11.Proofs.flashRoundIsSpec`
--| says it is `energy`, octopus by octopus.)
def Cavern.flashRound (cavern: Cavern) (flashed: Flashed): Flashed :=
  let has := flashed.lookup
  cavern.flash (at level => 9 < energyWith has at level)

--| Rounds until one adds nobody, at most `rounds` of them.
def Cavern.cascade (cavern: Cavern) (flashed: Flashed): (rounds: Nat) → Flashed
  | Zero => flashed
  | Succ more =>
    let next := cavern.flashRound flashed
    if next == flashed then flashed else cavern.cascade next more

--| The octopuses that flash in a step. Each round that adds somebody adds
--| an octopus, so after as many rounds as there are octopuses the next adds
--| nobody: that many is enough.
def Cavern.flashers (cavern: Cavern): Flashed := cavern.cascade cavern.noFlashers cavern.cells.length

--| One step: every octopus that flashed is at 0, the others at their
--| energy.
def Cavern.step (cavern: Cavern): Cavern :=
  let has := cavern.flashers.lookup
  cavern.map (at level => if has at then 0 else energyWith has at level)

--| The octopuses at 0 after a step: those that flashed in it.
def Cavern.zeros (cavern: Cavern): Nat := cavern.cells.count (((_, level)) => level == 0)

--| Whether every octopus is at 0.
def Cavern.allZero (cavern: Cavern): Bool := cavern.cells.all (((_, level)) => level == 0)

--| The flashes in `steps` steps from `cavern`.
def Cavern.flashesIn (cavern: Cavern): (steps: Nat) → Nat
  | Zero => 0
  | Succ more =>
    let next := cavern.step
    next.zeros + next.flashesIn more

def Cavern.solvePart1 (cavern: Cavern): Nat := cavern.flashesIn 100

--| How far part 2 looks.
def syncLimit: Nat := 10000

--| The first step, counting from `number`, after which every octopus is at
--| 0 (every one flashed in it), within `steps` steps.
def Cavern.firstSync (cavern: Cavern) (number: Nat): (steps: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := cavern.step
    if next.allZero then Some number else next.firstSync (Succ number) more

def Cavern.solvePart2 (cavern: Cavern): Option Nat := cavern.firstSync 1 syncLimit
