-- Advent of Code 2021, day 11: a grid of octopuses, each with an energy
-- level from 0 to 9. In a step every level goes up by 1; then each octopus
-- above 9 flashes, giving 1 more to each of the eight around it (diagonals
-- too), which can make them flash in turn; no octopus flashes twice in a
-- step, and every one that flashed ends the step at 0. Part 1 counts the
-- flashes in 100 steps; part 2 finds the first step in which every
-- octopus flashes.
--
--   $ cd aoc && stitchwort run Aoc.Year2021.Day11.main < inputs/2021/day11.txt
--
-- The puzzle input is committed in aoc/inputs/2021/.
--
-- A step works out who flashes in rounds: an octopus flashes once its
-- level, plus 1, plus the flashers around it so far, is above 9, and the
-- rounds go on until one adds nobody. The proofs that this is the
-- puzzle's step (the least set of flashers), and that both answers are
-- the puzzle's, are in `Aoc.Year2021.Day11.Proofs` (Proofs/); the tests in
-- `Aoc.Year2021.Day11.Tests` (Tests/). `run` checks neither.

namespace Aoc.Year2021.Day11
import Std (Fail, Fin, IO, List, Nat, Option, Parse, Text)
import Std.Parse (digit, many1)

def main(): {IO, Fail} () :=
  let levels := parseLevels IO.readAll()
  IO.print "Part 1: ${solvePart1 levels}"
  IO.print "Part 2: ${describe (solvePart2 levels)}"

-- One row of digits per line, every row as long as the first.
def parseLevels (input: Text): {Fail} (List (List Nat)) := checkRows (Parse.eachLine input (() => many1 digit))

-- The levels, if every row is as long as the first; otherwise fail, naming
-- the first that isn't.
def checkRows (rows: List (List (Fin 10))): {Fail} (List (List Nat)) :=
  match firstRagged rows with
    | Some (index, row) => Fail.fail "line ${index + 1}: expected ${width rows} digits, as on the first line, got ${row.length}"
    | None => numbers rows

-- The digits as numbers. (A function of its own: written in `checkRows`,
-- the `map` would run in `Fail`, and proofs would see the handler's
-- steps instead of a list.)
def numbers (rows: List (List (Fin 10))): List (List Nat) := rows.map (row => row.map Fin.toNat)

-- The first row's length.
def width (rows: List (List (Fin 10))): Nat := rows.headOr [] |> .length

-- The first row not as long as the first, with its index.
def firstRagged (rows: List (List (Fin 10))): Option (Nat, List (Fin 10)) :=
  rows.withIndex.find (((_, row)) => row.length != width rows)

-- `f` of every cell and its (row, column).
def mapCells (rows: List (List a)) (f: (Nat, Nat) → a → b): List (List b) :=
  rows.mapWithIndex (r row => row.mapWithIndex (c cell => f (r, c) cell))

-- The cell at (row, column); `None` off the grid.
def cellAt (rows: List (List a)) (at: (Nat, Nat)): Option a :=
  match rows.get at.fst with
    | Some row => row.get at.snd
    | None => None

-- The eight positions around `at`, diagonals included: none above row 0
-- or left of column 0, as positions are `Nat`s. Those past the far edges
-- are off the grid, where nothing has flashed (`flashedAt`).
def around (at: (Nat, Nat)): List (Nat, Nat) :=
  List.between (at.fst - 1) (at.fst + 1)
    |> .flatMap (r => List.between (at.snd - 1) (at.snd + 1) |> .map (c => (r, c)))
    |> .filter (near => not (near.fst == at.fst && near.snd == at.snd))

-- Whether the octopus at `at` has flashed (none off the grid has).
def flashedAt (flashed: List (List Bool)) (at: (Nat, Nat)): Bool := cellAt flashed at |> .getOrElse False

-- The level of the octopus at `at` in this step: its level before, plus
-- 1, plus 1 for each octopus around it that has flashed.
def energy (flashed: List (List Bool)) (at: (Nat, Nat)) (level: Nat): Nat := level + 1 + (around at).count (flashedAt flashed)

-- One round: an octopus flashes if its energy, given those that have
-- flashed so far, is above 9.
def flashRound (levels: List (List Nat)) (flashed: List (List Bool)): List (List Bool) :=
  mapCells levels (at level => 9 < energy flashed at level)

-- Rounds until one adds nobody, at most `rounds` of them.
def cascade (levels: List (List Nat)) (flashed: List (List Bool)): (rounds: Nat) → List (List Bool)
  | Zero => flashed
  | Succ more =>
    let next := flashRound levels flashed
    if next == flashed then flashed else cascade levels next more

-- The octopuses that flash in a step from `levels`. Each round that adds
-- somebody adds an octopus, so after as many rounds as there are
-- octopuses the next adds nobody: that many is enough.
def flashers (levels: List (List Nat)): List (List Bool) :=
  cascade levels (mapCells levels (_ _ => False)) levels.gridCells.length

-- One step: every octopus that flashed is at 0, the others at their
-- energy.
def step (levels: List (List Nat)): List (List Nat) :=
  let flashed := flashers levels
  mapCells levels (at level => if flashedAt flashed at then 0 else energy flashed at level)

-- The octopuses at 0 after a step: those that flashed in it.
def zeros (levels: List (List Nat)): Nat := levels.gridCells.count (((_, level)) => level == 0)

-- The flashes in `steps` steps from `levels`.
def flashesIn (levels: List (List Nat)): (steps: Nat) → Nat
  | Zero => 0
  | Succ more =>
    let next := step levels
    zeros next + flashesIn next more

def solvePart1 (levels: List (List Nat)): Nat := flashesIn levels 100

-- How far part 2 looks.
def syncLimit: Nat := 10000

-- The first step, counting from `number`, after which every octopus is at
-- 0 (every one flashed in it), within `steps` steps.
def firstSync (levels: List (List Nat)) (number: Nat): (steps: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := step levels
    if next.gridCells.all (((_, level)) => level == 0) then Some number else firstSync next (Succ number) more

def solvePart2 (levels: List (List Nat)): Option Nat := firstSync levels 1 syncLimit

def describe (answer: Option Nat): Text :=
  match answer with
    | Some number => "${number}"
    | None => "no step within ${syncLimit} has every octopus flash"
