-- Advent of Code 2024, day 6: a guard patrols a lab, stepping forward and
-- turning right whenever an obstruction is directly ahead, until she walks
-- off the map. Part 1 counts the distinct positions she visits. Part 2 counts
-- the positions where one new obstruction would trap her in a loop.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day06.main < inputs/2024/day06.txt
--
-- A walk need not end, so every walk carries a step budget: the guard has at
-- most `stateCount` states (a position and a facing), so a walk still on the
-- map after that many steps has repeated a state and loops forever.
--
-- The proofs are in `Aoc.Year2024.Day06.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day06.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day06
import Std (Fail, IO, List, Map, Nat, Option, Set, Text)

def main(): {IO, Fail} () :=
  let lab := parseLab IO.readAllLines()
  let part1 := solvePart1 lab |> .orFail "the guard never leaves the lab"
  let part2 := solvePart2 lab |> .orFail "the guard never leaves the lab"
  IO.print "Part 1: ${part1}"
  IO.print "Part 2: ${part2}"

type Position = { row: Nat, column: Nat }

type Direction =
  | Up
  | Right
  | Down
  | Left

def Direction.turnRight: Direction → Direction
  | Up => Right
  | Right => Down
  | Down => Left
  | Left => Up

-- Where the guard stands and which way she faces.
type Guard = { position: Position, facing: Direction }

-- The mapped area, `height` rows of `width` columns, its obstructions, and
-- where the guard starts, facing up.
type Lab = { height: Nat, width: Nat, obstructions: Set Position, start: Position }

-- What one character of the map shows.
type Cell =
  | Floor
  | Obstruction
  | GuardStart

-- One line per row, all as long as the first: `.` floor, `#` an obstruction,
-- `^` the guard. A failure names the line.
def parseLab (lines: List Text): {Fail} Lab :=
  let width := lines.headOr "" |> .length
  let cells :=
    lines
      |> .withIndex
      |> .map (((index, line)) => Fail.context "line ${index + 1}" (() => parseRow width line))
      |> .gridCells
      |> .map ((((row, column), cell)) => (({ row, column }: Position), cell))
  let positionsOf := (wanted: Cell) => cells.filter (cell => cell.snd == wanted) |> .map (cell => cell.fst)
  match positionsOf GuardStart with
    | [start] => { height = lines.length, width, obstructions = Set.fromList (positionsOf Obstruction), start }
    | [] => Fail.fail "expected a guard (^) on the map, found none"
    | _ => Fail.fail "expected one guard (^) on the map, found several"

def parseRow (width: Nat) (line: Text): {Fail} (List Cell) :=
  Fail.ensure (line.length == width) "expected ${width} characters, as on the first line, got ${line.length}"
  line.toList.map parseCell

def parseCell (ch: Char): {Fail} Cell :=
  match ch with
    | '.' => Floor
    | '#' => Obstruction
    | '^' => GuardStart
    | _ => Fail.fail "expected '.', '#' or '^', got '${ch}'"

-- The guard where the patrol begins.
def Lab.startGuard (lab: Lab): Guard := { position = lab.start, facing = Up }

-- The position directly in front of the guard, or `None` past the map's edge.
def Lab.ahead (lab: Lab) (guard: Guard): Option Position :=
  let { row, column } := guard.position
  match guard.facing with
    | Up => if row == 0 then None else Some ({ row = row - 1, column })
    | Right => if column + 1 < lab.width then Some ({ row, column = column + 1 }) else None
    | Down => if row + 1 < lab.height then Some ({ row = row + 1, column }) else None
    | Left => if column == 0 then None else Some ({ row, column = column - 1 })

-- One step of the protocol: turn right if something is directly in front,
-- else step forward. `None` once the guard leaves the mapped area.
def Lab.step (lab: Lab) (guard: Guard): Option Guard :=
  lab.ahead guard
    |> .map (next =>
      if lab.obstructions.contains next then { guard | facing = guard.facing.turnRight } else { guard | position = next })

-- How many states the guard can be in: a walk this long has repeated one.
def Lab.stateCount (lab: Lab): Nat := lab.height * lab.width * 4

-- The positions the guard visits before leaving, or `None` if she is still
-- on the map after `stateCount` steps, and so walks forever.
def Lab.patrol (lab: Lab): Option (Set Position) := lab.patrolFrom lab.startGuard Set.empty lab.stateCount

-- The walk from `guard`, adding each position to `visited`, for at most
-- `budget` more steps.
def Lab.patrolFrom (lab: Lab) (guard: Guard) (visited: Set Position): (budget: Nat) → Option (Set Position)
  | Zero => None
  | Succ budget =>
    let visitedNow := visited.insert guard.position
    match lab.step guard with
      | None => Some visitedNow
      | Some next => lab.patrolFrom next visitedNow budget

-- The lab with one more obstruction.
def Lab.withObstruction (lab: Lab) (position: Position): Lab :=
  { lab | obstructions = lab.obstructions.insert position }

-- The obstructions along each line: the columns of those in each row, and
-- the rows of those in each column. The guard walks straight to the nearest
-- one ahead.
type Sightlines = { byRow: Map Nat (Set Nat), byColumn: Map Nat (Set Nat) }

def Sightlines.of (obstructions: Set Position): Sightlines :=
  obstructions.foldLeft { byRow = Map.empty, byColumn = Map.empty } Sightlines.add

def Sightlines.add (sightlines: Sightlines) (obstruction: Position): Sightlines :=
  let { row, column } := obstruction
  {
    byRow = sightlines.byRow.insert row (sightlines.byRow.getOr row Set.empty |> .insert column),
    byColumn = sightlines.byColumn.insert column (sightlines.byColumn.getOr column Set.empty |> .insert row)
  }

-- Where the guard next turns: just short of the nearest obstruction ahead,
-- facing right of where she faced. `None` if nothing is ahead, so she walks
-- off the map.
def Sightlines.nextTurn (sightlines: Sightlines) (guard: Guard): Option Guard :=
  let { row, column } := guard.position
  let inRow := sightlines.byRow.getOr row Set.empty
  let inColumn := sightlines.byColumn.getOr column Set.empty
  let turnAt := (position: Position) => ({ position, facing = guard.facing.turnRight }: Guard)
  match guard.facing with
    | Up => inColumn.below row |> .map (obstruction => turnAt { row = obstruction + 1, column })
    | Right => inRow.above column |> .map (obstruction => turnAt { row, column = obstruction - 1 })
    | Down => inColumn.above row |> .map (obstruction => turnAt { row = obstruction - 1, column })
    | Left => inRow.below column |> .map (obstruction => turnAt { row, column = obstruction + 1 })

-- Whether the guard, from `guard`, walks forever: she reaches a state she
-- has been in before (`seen`). Every turn takes a step, so `budget` turns
-- are enough.
def Sightlines.loopsFrom (sightlines: Sightlines) (guard: Guard) (seen: Set Guard): (budget: Nat) → Bool
  | Zero => True
  | Succ budget =>
    match sightlines.nextTurn guard with
      | None => False
      | Some next => seen.contains next || sightlines.loopsFrom next (seen.insert next) budget

-- Whether the guard walks forever in `lab`, whose obstructions are
-- `sightlines`.
def Lab.loopsWith (lab: Lab) (sightlines: Sightlines): Bool :=
  sightlines.loopsFrom lab.startGuard (Set.singleton lab.startGuard) lab.stateCount

def Lab.loops (lab: Lab): Bool := lab.loopsWith (Sightlines.of lab.obstructions)

-- Part 1: the distinct positions visited; `None` if the guard never leaves.
def solvePart1 (lab: Lab): Option Nat := lab.patrol |> .map .size

-- Part 2: a new obstruction off the guard's route is never met, so only the
-- visited positions other than the start can trap her.
def solvePart2 (lab: Lab): Option Nat :=
  let sightlines := Sightlines.of lab.obstructions
  lab.patrol
    |> .map (visited => visited.filter (position => position != lab.start && lab.loopsWith (sightlines.add position)) |> .size)
