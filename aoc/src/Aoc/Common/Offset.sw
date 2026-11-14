--| Offsets: how far to move on a grid, in rows and columns, either way. A
--| `Position` is a cell of a board, so its row and column are `Nat`s; the
--| step from one cell to another, or a velocity, can go up or left, so an
--| `Offset` is two `Int`s. (Not `Vec`: std's sized lists have that name.)
--|
--| `b.offset (a.minus b)` is `Some a`; `position.offset offset` is `None`
--| when the row or the column would be negative, and `Grid.offset` also
--| off the grid. `wrap` is for a board whose edges wrap round. The proofs
--| are in `Aoc.Common.Proofs` (Proofs/Offset.sw), the tests in
--| `Aoc.Common.Tests` (Tests/Offset.sw).

namespace Aoc.Common
import Std (Int, Nat, Option)

--| How far to move: `rows` down (up when negative) and `columns` right
--| (left when negative).
type Offset = { rows: Int, columns: Int }

--| Staying put.
def Offset.zero: Offset := { rows = 0, columns = 0 }

def Offset.plus (offset other: Offset): Offset :=
  { rows = offset.rows + other.rows, columns = offset.columns + other.columns }

--| The same distance the other way.
def Offset.negate (offset: Offset): Offset := { rows = 0 - offset.rows, columns = 0 - offset.columns }

def Offset.times (offset: Offset) (factor: Int): Offset :=
  { rows = offset.rows * factor, columns = offset.columns * factor }

--| One step in `direction`. (`Aoc.Common.Proofs.stepOffset`: a step is an
--| offset by this.)
def Direction.offset: Direction → Offset
  | Up => { rows = -1, columns = 0 }
  | Right => { rows = 0, columns = 1 }
  | Down => { rows = 1, columns = 0 }
  | Left => { rows = 0, columns = -1 }

--| One step further in `direction`: for a day whose cells are offsets from
--| a corner, so that a step is always defined (2024's day 15).
def Offset.step (offset: Offset) (direction: Direction): Offset := offset.plus direction.offset

--| The offset from `from` to `position`.
def Position.minus (position from: Position): Offset :=
  { rows = position.row.toInt - from.row.toInt, columns = position.column.toInt - from.column.toInt }

--| The position `offset` away: `None` above row 0 or left of column 0.
--| Past the far edges there is no limit here; `Grid.offset` bounds it.
def Position.offset (position: Position) (offset: Offset): Option Position :=
  match (position.row.toInt + offset.rows).toNatChecked with
    | None => None
    | Some row =>
      match (position.column.toInt + offset.columns).toNatChecked with
        | None => None
        | Some column => Some { row, column }

--| The position `offset` away, if it is on the grid's rectangle.
def Grid.offset (grid: Grid a) (position: Position) (offset: Offset): Option Position :=
  match position.offset offset with
    | Some next => if grid.contains next then Some next else None
    | None => None

--| The position `offset` away on a board of `height` rows and `width`
--| columns whose edges wrap round: moving down past the last row comes back
--| in at the top, and up past the top in at the bottom; the same for
--| columns.
def Position.wrap (position: Position) (offset: Offset) (height width: Nat): Position := {
  row = Int.modNat (position.row.toInt + offset.rows) height,
  column = Int.modNat (position.column.toInt + offset.columns) width
}
