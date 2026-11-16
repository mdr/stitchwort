--| Facts about offsets: where `offset` lands, in `Int`s (`offsetSome`,
--| `offsetOf`), a step is an offset (`stepOffset`), and the laws a day
--| uses: by zero stays put, by `a.minus b` from `b` reaches `a`, offsets
--| compose with `plus` while the middle stays on the board, and back to
--| `minus`. On a wrapping board: `wrap` stays on it, wrapping twice is
--| wrapping by the sum, and wrapping by the same offset `n` times is
--| wrapping by `n` times it.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (And, Bool, Eq, Int, Nat, Option, Or, Void)

-- Equal parts

theorem positionExt ∀ (position other: Position)
    (rows: position.row = other.row)
    (columns: position.column = other.column):
    position = other :=
  match position, other with | { row, column }, { row = otherRow, column = otherColumn } => rewrite rows, columns

--| Positions are equal when their rows and columns are, as `Int`s.
theorem positionExtInt ∀ (position other: Position)
    (rows: position.row.toInt = other.row.toInt)
    (columns: position.column.toInt = other.column.toInt):
    position = other :=
  positionExt position other (arithmetic) (arithmetic)

theorem offsetExt ∀ (offset other: Offset)
    (sameRows: offset.rows = other.rows)
    (sameColumns: offset.columns = other.columns):
    offset = other :=
  match offset, other with
    | { rows, columns }, { rows = otherRows, columns = otherColumns } => rewrite sameRows, sameColumns

-- Where an offset lands

--| Where `offset` lands, as rows and columns.
theorem offsetSome ∀ (position: Position) (offset: Offset) (next: Position)
    (landed: position.offset offset = Some next):
    (next.row.toInt = position.row.toInt + offset.rows)
      ∧ (next.column.toInt = position.column.toInt + offset.columns) :=
  match rowAt: (position.row.toInt + offset.rows).toNatChecked with
    | Some row =>
      match columnAt: (position.column.toInt + offset.columns).toNatChecked with
        | Some column =>
          let same: ({ row, column }: Position) = next := Option.someInjective landed
          rewrite <- same then
            Both (Int.toNatCheckedSome _ row rowAt).flipped (Eq.flipped (Int.toNatCheckedSome _ column columnAt))

--| A position whose row and column are `offset` away is where it lands.
theorem offsetOf ∀ (position: Position) (offset: Offset) (next: Position)
    (rows: next.row.toInt = position.row.toInt + offset.rows)
    (columns: next.column.toInt = position.column.toInt + offset.columns):
    position.offset offset = Some next :=
  rewrite <- rows, <- columns then match next with | { row, column } => byComputing

--| `None` exactly when the row or the column would be negative.
theorem offsetNone ∀ (position: Position) (offset: Offset)
    (off: position.offset offset = None):
    (position.row.toInt + offset.rows < 0) ∨ (position.column.toInt + offset.columns < 0) :=
  match rowAt: (position.row.toInt + offset.rows).toNatChecked with
    | None => Inl (Int.toNatCheckedNone _ rowAt)
    | Some row =>
      match columnAt: (position.column.toInt + offset.columns).toNatChecked with
        | None => Inr (Int.toNatCheckedNone _ columnAt)

theorem offsetNoneOf ∀ (position: Position) (offset: Offset)
    (negative: (position.row.toInt + offset.rows < 0) ∨ (position.column.toInt + offset.columns < 0)):
    position.offset offset = None :=
  match landed: position.offset offset with
    | None => byComputing
    | Some next =>
      let both := offsetSome position offset next landed
      match negative with
        | Inl below => Void.impossible (arithmetic [both.left])
        | Inr before => Void.impossible (arithmetic [both.right])

--| A step is an offset by its direction's.
theorem stepOffset ∀ (position: Position) (direction: Direction):
    position.step direction = position.offset direction.offset :=
  match position, direction with
    | { row = Zero, column }, Up =>
      Eq.flipped (offsetNoneOf { row = Zero, column } (Direction.offset Up) (Inl (arithmetic)))
    | { row = Succ above, column }, Up =>
      Eq.flipped
        (offsetOf { row = Succ above, column } (Direction.offset Up) { row = above, column } (arithmetic) (arithmetic))
    | { row, column }, Right =>
      Eq.flipped
        (offsetOf { row, column } (Direction.offset Right) { row, column = column + 1 } (arithmetic) (arithmetic))
    | { row, column }, Down =>
      Eq.flipped (offsetOf { row, column } (Direction.offset Down) { row = row + 1, column } (arithmetic) (arithmetic))
    | { row, column = Zero }, Left =>
      Eq.flipped (offsetNoneOf { row, column = Zero } (Direction.offset Left) (Inr (arithmetic)))
    | { row, column = Succ before }, Left =>
      Eq.flipped
        (offsetOf
          { row, column = Succ before }
          (Direction.offset Left)
          { row, column = before }
          (arithmetic)
          (arithmetic))

-- The laws

--| By zero stays put.
theorem offsetZero ∀ (position: Position): position.offset Offset.zero = Some position :=
  offsetOf position Offset.zero position (arithmetic) (arithmetic)

--| From `from`, the offset to `position` reaches it.
theorem offsetMinus ∀ (position from: Position): from.offset (position.minus from) = Some position :=
  offsetOf from (position.minus from) position (arithmetic) (arithmetic)

--| Where an offset lands is that offset away.
theorem minusOffset ∀ (position: Position) (offset: Offset) (next: Position)
    (landed: position.offset offset = Some next):
    next.minus position = offset :=
  let both := offsetSome position offset next landed
  offsetExt (next.minus position) offset (arithmetic [both.left]) (arithmetic [both.right])

--| Two offsets in turn are their sum, when the middle is on the board.
theorem offsetPlus ∀ (position: Position) (first second: Offset) (middle: Position)
    (landed: position.offset first = Some middle):
    middle.offset second = position.offset (first.plus second) :=
  let both := offsetSome position first middle landed
  match after: middle.offset second with
    | Some next =>
      let more := offsetSome middle second next after
      Eq.flipped
        (offsetOf position
          (first.plus second)
          next
          (arithmetic [both.left, more.left])
          (arithmetic [both.right, more.right]))
    | None =>
      Eq.flipped
        (offsetNoneOf position
          (first.plus second)
          (match offsetNone middle second after with
            | Inl below => Inl (arithmetic [both.left])
            | Inr before => Inr (arithmetic [both.right])))

--| The offset back is the negation.
theorem minusNegate ∀ (position from: Position): (position.minus from).negate = from.minus position :=
  offsetExt (position.minus from).negate (from.minus position) (arithmetic) (arithmetic)

theorem minusSelf ∀ (position: Position): position.minus position = Offset.zero :=
  offsetExt (position.minus position) Offset.zero (arithmetic) (arithmetic)

--| Steps of offsets: different offsets step to different ones, two steps
--| can be taken in either order, and the opposite step undoes one.
theorem offsetStepInjective ∀ (offset other: Offset) (direction: Direction)
    (same: offset.step direction = other.step direction):
    offset = other :=
  offsetExt offset other (arithmetic [Eq.cong Offset.rows same]) (arithmetic [Eq.cong Offset.columns same])

theorem offsetStepComm ∀ (offset: Offset) (first second: Direction):
    (offset.step first).step second = (offset.step second).step first :=
  offsetExt ((offset.step first).step second) ((offset.step second).step first) (arithmetic) (arithmetic)

theorem offsetStepOpposite ∀ (offset: Offset) (direction: Direction):
    (offset.step direction).step direction.opposite = offset :=
  match direction with
    | Up => offsetExt ((offset.step Up).step Down) offset (arithmetic) (arithmetic)
    | Right => offsetExt ((offset.step Right).step Left) offset (arithmetic) (arithmetic)
    | Down => offsetExt ((offset.step Down).step Up) offset (arithmetic) (arithmetic)
    | Left => offsetExt ((offset.step Left).step Right) offset (arithmetic) (arithmetic)

-- On a grid

--| `Grid.offset` is `offset`, kept to the grid.
theorem gridOffsetSome ∀ (grid: Grid a) (position: Position) (offset: Offset) (next: Position)
    (landed: grid.offset position offset = Some next):
    (position.offset offset = Some next) ∧ (grid.contains next = True) :=
  match found: position.offset offset with
    | Some here =>
      match inside: grid.contains here with
        | True =>
          let same: here = next := Option.someInjective landed
          rewrite <- same then Both byComputing inside

theorem gridOffsetOf ∀ (grid: Grid a) (position: Position) (offset: Offset) (next: Position)
    (landed: position.offset offset = Some next)
    (inside: grid.contains next = True):
    grid.offset position offset = Some next :=
  rewrite landed, inside

-- On a board that wraps

--| `wrap` stays on the board.
theorem wrapWithin ∀ (position: Position) (offset: Offset) (height width: Nat)
    [auto tall: height ≠ 0]
    [auto wide: width ≠ 0]:
    (position.wrap offset height width).within height width = True :=
  let rowBelow := Int.modNatLt (position.row.toInt + offset.rows) height [ok := tall]
  let columnBelow := Int.modNatLt (position.column.toInt + offset.columns) width [ok := wide]
  Both (arithmetic [rowBelow]) (arithmetic [columnBelow])

--| By zero, a position on the board stays put.
theorem wrapZero ∀ (position: Position) (height width: Nat)
    (inside: position.within height width = True):
    position.wrap Offset.zero height width = position :=
  positionExt
    (position.wrap Offset.zero height width)
    position
    (rewrite (arithmetic: position.row.toInt + 0 = position.row.toInt) then
      Int.modNatOfLt height position.row (arithmetic [inside.left]))
    (rewrite (arithmetic: position.column.toInt + 0 = position.column.toInt) then
      Int.modNatOfLt width position.column (arithmetic [inside.right]))

--| Wrapping twice is wrapping by the sum.
theorem wrapPlus ∀ (position: Position) (first second: Offset) (height width: Nat)
    [auto tall: height ≠ 0]
    [auto wide: width ≠ 0]:
    (position.wrap first height width).wrap second height width = position.wrap (first.plus second) height width :=
  positionExt
    ((position.wrap first height width).wrap second height width)
    (position.wrap (first.plus second) height width)
    (Eq.trans
      (Int.modNatModAdd (position.row.toInt + first.rows) second.rows height [ok := tall])
      (Eq.cong (x => Int.modNat x height) (arithmetic)))
    (Eq.trans
      (Int.modNatModAdd (position.column.toInt + first.columns) second.columns width [ok := wide])
      (Eq.cong (x => Int.modNat x width) (arithmetic)))

--| Wrapping by `offset` `times` times is wrapping by `times` times it, from
--| a position on the board.
theorem wrapIterate ∀ (offset: Offset) (height width: Nat)
    [auto tall: height ≠ 0]
    [auto wide: width ≠ 0]
    (times: Nat) (position: Position)
    (inside: position.within height width = True):
    times.iterate (here => here.wrap offset height width) position
      = position.wrap (offset.times times.toInt) height width :=
  match times with
    | Zero =>
      Eq.flipped
        (Eq.trans
          (Eq.cong
            (moved => position.wrap moved height width)
            (offsetExt (offset.times (Nat.toInt 0)) Offset.zero (arithmetic) (arithmetic)))
          (wrapZero position height width inside))
    | Succ times =>
      calc (Succ times).iterate (here => here.wrap offset height width) position
        _ = (position.wrap offset height width).wrap (offset.times times.toInt) height width :=
          wrapIterate offset height width times
            (position.wrap offset height width)
            (wrapWithin position offset height width)
        _ = position.wrap (offset.plus (offset.times times.toInt)) height width :=
          wrapPlus position offset (offset.times times.toInt) height width
        _ = position.wrap (offset.times (Succ times).toInt) height width :=
          Eq.cong
            (moved => position.wrap moved height width)
            (offsetExt (offset.plus (offset.times times.toInt)) (offset.times (Succ times).toInt) (algebra) (algebra))
