--| Advent of Code 2020, day 17: Conway Cubes. An infinite grid of cubes,
--| each active or inactive; the input is a flat slice of it (`#` active,
--| `.` inactive), and every other cube starts inactive. In a cycle every
--| cube changes at once, by how many of its neighbours (the cubes within 1
--| in every coordinate) are active: an active cube stays active with 2 or
--| 3, an inactive one becomes active with exactly 3. Each part is how many
--| cubes are active after six cycles: in three dimensions in part 1, in
--| four in part 2.
--|
--|   $ cd aoc && stitchwort run Aoc.Year2020.Day17.main < inputs/2020/day17.txt
--|
--| A cube is a list of coordinates, so one program serves every number of
--| dimensions. A cycle (`Aoc.Common.lifeStep`) counts, for each active cube, one for
--| each of its neighbours, so only the cubes next to an active one are ever looked at.
--| The proofs, that the parser reads the puzzle's format and that a cycle
--| is the puzzle's cycle, cube by cube, are in `Aoc.Year2020.Day17.Proofs`
--| (Proofs/), and the tests in `Aoc.Year2020.Day17.Tests` (Tests/); `run`
--| checks neither.

namespace Aoc.Year2020.Day17
import Aoc.Common (Grid, Position, lifeStep, parseGrid)
import Std (Bool, Eq, Fail, IO, Int, List, Nat, Ord, Parse, Set)

def main(): {IO, Fail} () :=
  let slice := parseSlice IO.readAll()
  IO.print "Part 1: ${slice.pocket (dimensions := 3) |> .boot |> .activeCount}"
  IO.print "Part 2: ${slice.pocket (dimensions := 4) |> .boot |> .activeCount}"

type CubeState = | Active | Inactive

--| How the slice writes a cube's state.
def CubeState.symbol: CubeState → Text
  | Active => "#"
  | Inactive => "."

def cubeState(): {Parse} CubeState := Parse.pick ([Active, Inactive].map (state => (state.symbol, state)))

--| The input: the cubes of one flat slice, a row a line.
type Slice = { grid: Grid CubeState }

--| One row of the slice per line, every row as long as the first.
def parseSlice (input: Text): {Fail} Slice := { grid = parseGrid input cubeState }

--| A cube, by its coordinates: `x`, `y`, then one for each further
--| dimension.
type Cube = { coordinates: List Int }

--| Ordered by coordinates, so cubes can be the keys of a `Map` and a `Set`.
instance Cube.instOrd: Ord Cube := Ord.byKey (cube => cube.coordinates) (a b same => Cube.ext a b same)

--| Every list of coordinates within 1 of `coordinates` in each place,
--| `coordinates` itself among them: 3 ^ n lists of n.
def within1: List Int → List (List Int)
  | [] => [[]]
  | [coordinate, ..rest] =>
    let others := within1 rest
    [coordinate - 1, coordinate, coordinate + 1].flatMap (here => others.map (more => [here, ..more]))

--| The cubes within 1 of this one in every coordinate, other than itself:
--| 26 in three dimensions, 80 in four.
def Cube.neighbours (cube: Cube): List Cube :=
  within1 cube.coordinates
    |> .filter (coordinates => coordinates != cube.coordinates)
    |> .map (coordinates => { coordinates })

--| The cube at a position of the slice, in `dimensions` dimensions: the
--| column is `x`, the row `y`, and every further coordinate 0.
def Cube.inSlice (dimensions: Nat) (at: Position): Cube :=
  { coordinates = [at.column.toInt, at.row.toInt, ..List.replicate (dimensions - 2) 0] }

--| The active cubes; every other cube is inactive.
type Pocket = { active: Set Cube }

--| The pocket before any cycle: the slice's active cubes, in `dimensions`
--| dimensions.
def Slice.pocket (slice: Slice) (dimensions: Nat): Pocket :=
  { active = slice.grid.positionsWhere (== Active) |> .map (Cube.inSlice dimensions) |> .toSet }

--| Whether a cube that is (or isn't) `active`, with `count` active
--| neighbours, is active after the cycle.
def lifeRule (active: Bool) (count: Nat): Bool := count == 3 || (count == 2 && active)

--| Every cube changes at once: `lifeStep` counts the active cubes each cube
--| neighbours, and a cube next to none is inactive after the cycle.
def Pocket.cycle (pocket: Pocket): Pocket := { active = lifeStep Cube.neighbours lifeRule pocket.active }

--| "Starting with your given initial configuration, simulate six cycles."
def Pocket.boot (pocket: Pocket): Pocket := Nat.iterate 6 Pocket.cycle pocket

def Pocket.activeCount (pocket: Pocket): Nat := pocket.active.size
