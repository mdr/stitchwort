--| Day 17 as the puzzle states it: how the slice is written, which cubes
--| it makes active at the start, a cycle cube by cube, and the answer, the
--| number of active cubes after six cycles. The state is the set of active
--| cubes; nothing is shared with the program but the data types (`Slice`,
--| `CubeState`, `Cube`, with its order for the `Set`). The proofs (Proofs/)
--| show the program computes these.

namespace Aoc.Year2020.Day17.Spec
import Aoc.Year2020.Day17 (Cube, CubeState, Slice)
import Std (Int, List, Nat, Set)

-- The format

--| Each cube of the slice "is either active (`#`) or inactive (`.`)".
def symbol: CubeState → Char
  | Active => '#'
  | Inactive => '.'

--| A line of the input is its row of the slice, a cube a character.
def RowWritten (line: List Char) (row: List CubeState): Prop := line = row.map symbol

-- The start

--| "In the initial state of the pocket dimension, almost all cubes start
--| inactive. The exception to this is a small flat region of cubes (your
--| puzzle input)": the cube with `x` the column and `y` the row of an
--| active cube in the slice, and every further coordinate 0 ("z=0"), is
--| active; no other cube is.
def Starts (slice: Slice) (dimensions: Nat) (start: Set Cube): Prop :=
  ∀ (cube: Cube) => (start.contains cube = True)
    ↔ (∃ (x: Nat) => ∃ (y: Nat) => slice.grid.at { row = y, column = x } = Some Active
      ∧ cube.coordinates = [x.toInt, y.toInt, ..List.replicate (dimensions - 2) 0])

-- A cycle

--| As many coordinates in each list, and each differs from the other's by
--| at most 1.
def within1: List Int → List Int → Bool
  | [], [] => True
  | [a, ..rest], [b, ..others] => a - 1 <= b && b <= a + 1 && within1 rest others
  | _, _ => False

--| "Its neighbors are any of the 26 other cubes where any of their
--| coordinates differ by at most 1": `other` is a different cube, within 1
--| in every coordinate.
def neighbours (other cube: Cube): Bool := other != cube && within1 other.coordinates cube.coordinates

--| How many of the cube's neighbours are active.
def activeNeighbours (active: Set Cube) (cube: Cube): Nat := active.count (other => neighbours other cube)

--| "If a cube is active and exactly 2 or 3 of its neighbors are also
--| active, the cube remains active. Otherwise, the cube becomes inactive.
--| If a cube is inactive but exactly 3 of its neighbors are active, the
--| cube becomes active. Otherwise, the cube remains inactive."
def activeAfter (active: Set Cube) (cube: Cube): Bool :=
  let near := activeNeighbours active cube
  if active.contains cube then near == 2 || near == 3 else near == 3

--| "During a cycle, all cubes simultaneously change their state": a cube
--| is active after the cycle exactly when the rules make it so, from the
--| cubes active before.
def Cycle (before after: Set Cube): Prop := ∀ (cube: Cube) => after.contains cube = activeAfter before cube

--| `cycles` cycles take the active cubes `start` to `final`.
def Cycles: (cycles: Nat) → (start: Set Cube) → (final: Set Cube) → Prop
  | Zero, start, final => final = start
  | Succ more, start, final => ∃ (next: Set Cube) => Cycle start next ∧ Cycles more next final

-- The answer

--| "Starting with your given initial configuration, simulate six cycles.
--| How many cubes are left in the active state after the sixth cycle?",
--| with the pocket in `dimensions` dimensions: 3 in part 1, 4 in part 2.
def Answer (slice: Slice) (dimensions answer: Nat): Prop :=
  ∃ (start: Set Cube) => ∃ (final: Set Cube) => Starts slice dimensions start
    ∧ Cycles 6 start final
    ∧ answer = final.size
