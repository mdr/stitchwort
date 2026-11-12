--| Advent of Code 2024, day 18: bytes fall one at a time onto a square
--| memory space, corrupting the positions they land on. Part 1 is the fewest
--| steps from the top left corner to the bottom right one after the first
--| bytes have fallen; part 2 is the first byte whose fall leaves no way
--| through.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day18.main < inputs/2024/day18.txt
--|   $ cd aoc && stitchwort run Aoc.Year2024.Day18.main -- 7 12 < examples/2024/day18.txt
--|
--| The proofs are in `Aoc.Year2024.Day18.Proofs` (Proofs/) and the tests in
--| `Aoc.Year2024.Day18.Tests` (Tests/); `run` checks neither. Positions and
--| the graph of steps between neighbours are the shared grid code's
--| (`Aoc.Common`, Common/Grid.sw and GridGraph.sw).

namespace Aoc.Year2024.Day18
import Aoc.Common (Position, memPositionsOfWithin, positions, stepGraph)
import Std (Bool, Fail, Graph, IO, List, Map, Nat, Option, Parse, Set, Text, Void)
import Std.Parse (nat, text)

--| The memory space is the puzzle's, 71 positions each way, after 1024
--| bytes, unless the arguments give a size and a number of bytes: `-- 7 12`
--| for the example's.
def main(): {IO, Fail} () :=
  let (size, fallen) := sizesFrom IO.args()
  let bytes := parseBytes IO.readAll()
  IO.print "Part 1: ${solvePart1 size fallen bytes |> .orFail "no path to the exit once the first ${fallen} bytes have fallen"}"
  let blocker := solvePart2 size bytes |> .orFail "no byte cuts the exit off"
  IO.print "Part 2: ${blocker.column},${blocker.row}"

def sizesFrom (args: List Text): {Fail} (Nat, Nat) :=
  let usage := "expected no arguments, or a size and a number of bytes, such as `7 12`"
  match args with
    | [] => (71, 1024)
    | [sizeText, fallenText] => (Fail.need sizeText.toNat usage, Fail.need fallenText.toNat usage)
    | _ => Fail.fail usage

--| One byte's position: "5,4" is X = 5 from the left edge, its column, and
--| Y = 4 from the top, its row.
def byte(): {Parse} Position :=
  let x := nat()
  text ","
  let y := nat()
  { row = y, column = x }

--| One byte per line, in the order they fall.
def parseBytes (input: Text): {Fail} List Position := Parse.eachLine input byte

--| The memory space, `size` positions each way, and its corrupted positions.
type MemorySpace = { size: Nat, corrupted: Set Position }

--| The memory space once the first `fallen` bytes have fallen.
def MemorySpace.after (size: Nat) (bytes: List Position) (fallen: Nat): MemorySpace := { size, corrupted = bytes.take fallen |> .toSet }

--| Inside the memory space and not corrupted.
def MemorySpace.isSafe (memory: MemorySpace) (position: Position): Bool :=
  position.within memory.size memory.size && !memory.corrupted.contains position

--| Entering a safe position takes one step; nothing else can be entered.
def MemorySpace.enter (memory: MemorySpace) (position: Position): Option Nat := if memory.isSafe position then Some 1 else None

--| A position that can be entered is inside the memory space.
theorem MemorySpace.enterListed (memory: MemorySpace) (position: Position) (cost: Nat) (found: memory.enter position = Some cost):
    position ∈ positions memory.size memory.size :=
  match safe: memory.isSafe position with
    | True => memPositionsOfWithin memory.size memory.size position (Bool.andLeft safe)

--| The memory space as a graph for std's search: a step from each position
--| to each safe neighbour (up, right, down or left).
def MemorySpace.graph (memory: MemorySpace): Graph Position :=
  stepGraph memory.enter (positions memory.size memory.size) (position cost found => memory.enterListed position cost found)

--| The top left corner, where the search starts.
def topLeft: Position := { row = 0, column = 0 }

--| The bottom right corner.
def MemorySpace.exit (memory: MemorySpace): Position := { row = memory.size - 1, column = memory.size - 1 }

--| The fewest steps from the start to each position reachable from it, by
--| breadth-first search; none if the start is corrupted.
def MemorySpace.fromStart (memory: MemorySpace): Map Position Nat := if memory.isSafe topLeft then memory.graph.breadthFirst [topLeft] else Map.empty

def MemorySpace.fewestSteps (memory: MemorySpace): Option Nat := memory.fromStart.get memory.exit

--| Whether the exit can be reached once the first `fallen` bytes have
--| fallen.
def reachable (size: Nat) (bytes: List Position) (fallen: Nat): Bool := (MemorySpace.after size bytes fallen).fewestSteps.isSome

def solvePart1 (size: Nat) (fallen: Nat) (bytes: List Position): Option Nat := (MemorySpace.after size bytes fallen).fewestSteps

--| A binary search for the first number of bytes fallen that leaves no way
--| through (the exit can't become reachable again once it isn't); none if
--| that is before any byte falls, or never.
def solvePart2 (size: Nat) (bytes: List Position): Option Position :=
  match Nat.partitionPoint 0 (bytes.length + 1) (reachable size bytes) with
    | Zero => None
    | Succ index => bytes.get index
