-- Advent of Code 2024, day 18: bytes fall one at a time onto a square
-- memory space, corrupting the positions they land on. Part 1 is the fewest
-- steps from the top left corner to the bottom right one after the first
-- bytes have fallen; part 2 is the first byte whose fall leaves no way
-- through.
--
--   $ cd aoc && stitchwort run Aoc.Year2024.Day18.main < inputs/2024/day18.txt
--   $ cd aoc && stitchwort run Aoc.Year2024.Day18.mainExample < examples/2024/day18.txt
--
-- The proofs are in `Aoc.Year2024.Day18.Proofs` (Proofs/) and the tests in
-- `Aoc.Year2024.Day18.Tests` (Tests/); `run` checks neither.

namespace Aoc.Year2024.Day18
import Aoc.Year2024.Day16 (Graph)
import Std (Bool, Fail, IO, List, Map, Nat, Option, Parse, Set, Text)
import Std.Parse (nat, text)

-- The puzzle's memory space, 71 positions each way, after 1024 bytes.
def main(): {IO, Fail} () := solveIn 71 1024

-- The example's memory space, 7 positions each way, after 12 bytes.
def mainExample(): {IO, Fail} () := solveIn 7 12

def solveIn (size: Nat) (fallen: Nat): {IO, Fail} () :=
  let bytes := parseBytes IO.readAll()
  IO.print "Part 1: ${solvePart1 size fallen bytes |> .fold "none" Nat.toText}"
  IO.print "Part 2: ${solvePart2 size bytes |> .fold "none" (byte => "${byte.x},${byte.y}")}"

-- `x` positions from the left edge, `y` from the top.
type Position = { x: Nat, y: Nat }

-- One byte's position: "5,4".
def byte(): {Parse} Position :=
  let x := nat()
  text ","
  let y := nat()
  { x, y }

-- One byte per line, in the order they fall.
def parseBytes (input: Text): {Fail} (List Position) := Parse.eachLine input byte

-- The memory space, `size` positions each way, and its corrupted positions.
type MemorySpace = { size: Nat, corrupted: Set Position }

-- The memory space once the first `fallen` bytes have fallen.
def MemorySpace.after (size: Nat) (bytes: List Position) (fallen: Nat): MemorySpace := { size, corrupted = bytes.take fallen |> Set.fromList }

-- Inside the memory space and not corrupted.
def MemorySpace.isSafe (memory: MemorySpace) (position: Position): Bool :=
  position.x < memory.size && position.y < memory.size && !memory.corrupted.contains position

type Direction =
  | Up
  | Down
  | Left
  | Right

def directions: List Direction := [Up, Down, Left, Right]

-- The position one step in `direction`; none above the top or left of the
-- left edge.
def Position.step (position: Position): Direction → Option Position
  | Down => Some ({ position | y = Succ position.y })
  | Right => Some ({ position | x = Succ position.x })
  | Up =>
    match position.y with
      | Zero => None
      | Succ above => Some ({ position | y = above })
  | Left =>
    match position.x with
      | Zero => None
      | Succ before => Some ({ position | x = before })

-- The position one step in `direction`, if it's safe.
def MemorySpace.move (memory: MemorySpace) (position: Position) (direction: Direction): Option Position :=
  match position.step direction with
    | Some next => if memory.isSafe next then Some next else None
    | None => None

-- The safe positions one step away, each one step.
def MemorySpace.edges (memory: MemorySpace) (position: Position): List (Position, Nat) :=
  directions.filterMap (direction => memory.move position direction |> .map (next => (next, 1)))

-- Every position inside the memory space.
def MemorySpace.positions (memory: MemorySpace): List Position :=
  List.range memory.size |> .flatMap (x => List.range memory.size |> .map (y => ({ x, y }: Position)))

-- A safe position is on the list of all of them.
theorem MemorySpace.safeListed (memory: MemorySpace): (position: Position) → memory.isSafe position = True → position ∈ memory.positions
  | { x, y }, safe =>
    let xInside := Bool.andLeft _ _ safe
    let yInside := Bool.andLeft _ _ (Bool.andRight _ _ safe)
    List.memFlatMapIntro (column => List.range memory.size |> .map (row => ({ x = column, y = row }: Position))) x ({ x, y }: Position)
      (List.range memory.size) (List.memRangeFromIntro x memory.size 0 rfl (omega [xInside]))
      (List.memMap (List.range memory.size) y (List.memRangeFromIntro y memory.size 0 rfl (omega [yInside])) (row => ({ x, y = row }: Position)))

-- The memory space as a graph for day 16's search: safe positions, each a
-- step from its safe neighbours.
def MemorySpace.graph (memory: MemorySpace): Graph Position := {
  edges = memory.edges,
  within = memory.isSafe,
  states = memory.positions,
  listed = position => memory.safeListed position
}

def start: Position := { x = 0, y = 0 }

-- The bottom right corner.
def MemorySpace.exit (memory: MemorySpace): Position := { x = memory.size - 1, y = memory.size - 1 }

-- The fewest steps from the start to each position reachable from it; none
-- if the start is corrupted.
def MemorySpace.fromStart (memory: MemorySpace): Map Position Nat :=
  if memory.isSafe start then memory.graph.distances [(start, 0)] else Map.empty

def MemorySpace.fewestSteps (memory: MemorySpace): Option Nat := memory.fromStart.get memory.exit

-- Whether the exit can be reached once the first `fallen` bytes have
-- fallen.
opaque def reachable (size: Nat) (bytes: List Position) (fallen: Nat): Bool := (MemorySpace.after size bytes fallen).fewestSteps.isSome

-- A binary search for a count `blocked` holds for, just after one it
-- fails for, given that it fails at `low` and holds at `high`.
def firstBlocked (blocked: Nat → Bool) (low: Nat) (high: Nat): Nat
    decreasing high - low :=
  if apart: Succ low < high then
    let middle := (low + high) / 2
    if blocked middle then firstBlocked blocked low middle [decreasing := omega [apart]]
    else firstBlocked blocked middle high [decreasing := omega [apart]]
  else high

def solvePart1 (size: Nat) (fallen: Nat) (bytes: List Position): Option Nat := (MemorySpace.after size bytes fallen).fewestSteps

-- A binary search over how many bytes have fallen: the exit can't become
-- reachable again once it isn't.
def solvePart2 (size: Nat) (bytes: List Position): Option Position :=
  let blocked := (fallen: Nat) => !reachable size bytes fallen
  if blocked 0 || !blocked bytes.length then None else bytes.get (firstBlocked blocked 0 bytes.length - 1)
