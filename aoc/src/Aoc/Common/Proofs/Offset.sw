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
  match position, other with | { row, column }, { row = otherRow, column = otherColumn } => rewrite rows, columns in rfl

--| Positions are equal when their rows and columns are, as `Int`s.
theorem positionExtInt ∀ (position other: Position)
    (rows: position.row.toInt = other.row.toInt)
    (columns: position.column.toInt = other.column.toInt):
    position = other :=
  positionExt position other (omega) (omega)

theorem offsetExt ∀ (offset other: Offset)
    (sameRows: offset.rows = other.rows)
    (sameColumns: offset.columns = other.columns):
    offset = other :=
  match offset, other with
    | { rows, columns }, { rows = otherRows, columns = otherColumns } => rewrite sameRows, sameColumns in rfl

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
          rewrite <- same in
            Both (Eq.sym (Int.toNatCheckedSome _ row rowAt)) (Eq.sym (Int.toNatCheckedSome _ column columnAt))

--| A position whose row and column are `offset` away is where it lands.
theorem offsetOf ∀ (position: Position) (offset: Offset) (next: Position)
    (rows: next.row.toInt = position.row.toInt + offset.rows)
    (columns: next.column.toInt = position.column.toInt + offset.columns):
    position.offset offset = Some next :=
  rewrite <- rows, <- columns in match next with | { row, column } => rfl

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
    | None => rfl
    | Some next =>
      let both := offsetSome position offset next landed
      match negative with
        | Inl below => Void.exfalso (omega [And.left both])
        | Inr before => Void.exfalso (omega [And.right both])

--| A step is an offset by its direction's.
theorem stepOffset ∀ (position: Position) (direction: Direction):
    position.step direction = position.offset direction.offset :=
  match position, direction with
    | { row = Zero, column }, Up => Eq.sym (offsetNoneOf { row = Zero, column } (Direction.offset Up) (Inl (omega)))
    | { row = Succ above, column }, Up =>
      Eq.sym (offsetOf { row = Succ above, column } (Direction.offset Up) { row = above, column } (omega) (omega))
    | { row, column }, Right =>
      Eq.sym (offsetOf { row, column } (Direction.offset Right) { row, column = column + 1 } (omega) (omega))
    | { row, column }, Down =>
      Eq.sym (offsetOf { row, column } (Direction.offset Down) { row = row + 1, column } (omega) (omega))
    | { row, column = Zero }, Left => Eq.sym (offsetNoneOf { row, column = Zero } (Direction.offset Left) (Inr (omega)))
    | { row, column = Succ before }, Left =>
      Eq.sym (offsetOf { row, column = Succ before } (Direction.offset Left) { row, column = before } (omega) (omega))

-- The laws

--| By zero stays put.
theorem offsetZero ∀ (position: Position): position.offset Offset.zero = Some position :=
  offsetOf position Offset.zero position (omega) (omega)

--| From `from`, the offset to `position` reaches it.
theorem offsetMinus ∀ (position from: Position): from.offset (position.minus from) = Some position :=
  offsetOf from (position.minus from) position (omega) (omega)

--| Where an offset lands is that offset away.
theorem minusOffset ∀ (position: Position) (offset: Offset) (next: Position)
    (landed: position.offset offset = Some next):
    next.minus position = offset :=
  let both := offsetSome position offset next landed
  offsetExt (next.minus position) offset (omega [And.left both]) (omega [And.right both])

--| Two offsets in turn are their sum, when the middle is on the board.
theorem offsetPlus ∀ (position: Position) (first second: Offset) (middle: Position)
    (landed: position.offset first = Some middle):
    middle.offset second = position.offset (first.plus second) :=
  let both := offsetSome position first middle landed
  match after: middle.offset second with
    | Some next =>
      let more := offsetSome middle second next after
      Eq.sym
        (offsetOf position
          (first.plus second)
          next
          (omega [And.left both, And.left more])
          (omega [And.right both, And.right more]))
    | None =>
      Eq.sym
        (offsetNoneOf position
          (first.plus second)
          (match offsetNone middle second after with
            | Inl below => Inl (omega [And.left both])
            | Inr before => Inr (omega [And.right both])))

--| The offset back is the negation.
theorem minusNegate ∀ (position from: Position): (position.minus from).negate = from.minus position :=
  offsetExt (position.minus from).negate (from.minus position) (omega) (omega)

theorem minusSelf ∀ (position: Position): position.minus position = Offset.zero :=
  offsetExt (position.minus position) Offset.zero (omega) (omega)

--| Steps of offsets: different offsets step to different ones, two steps
--| can be taken in either order, and the opposite step undoes one.
theorem offsetStepInjective ∀ (offset other: Offset) (direction: Direction)
    (same: offset.step direction = other.step direction):
    offset = other :=
  offsetExt offset other (omega [Eq.cong Offset.rows same]) (omega [Eq.cong Offset.columns same])

theorem offsetStepComm ∀ (offset: Offset) (first second: Direction):
    (offset.step first).step second = (offset.step second).step first :=
  offsetExt ((offset.step first).step second) ((offset.step second).step first) (omega) (omega)

theorem offsetStepOpposite ∀ (offset: Offset) (direction: Direction):
    (offset.step direction).step direction.opposite = offset :=
  match direction with
    | Up => offsetExt ((offset.step Up).step Down) offset (omega) (omega)
    | Right => offsetExt ((offset.step Right).step Left) offset (omega) (omega)
    | Down => offsetExt ((offset.step Down).step Up) offset (omega) (omega)
    | Left => offsetExt ((offset.step Left).step Right) offset (omega) (omega)

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
          rewrite <- same in Both rfl inside

theorem gridOffsetOf ∀ (grid: Grid a) (position: Position) (offset: Offset) (next: Position)
    (landed: position.offset offset = Some next)
    (inside: grid.contains next = True):
    grid.offset position offset = Some next :=
  rewrite landed, inside in rfl

-- On a board that wraps

--| `wrap` stays on the board.
theorem wrapWithin ∀ (position: Position) (offset: Offset) (height width: Nat)
    [auto tall: height ≠ 0]
    [auto wide: width ≠ 0]:
    (position.wrap offset height width).within height width = True :=
  let rowBelow := Int.modNatLt (position.row.toInt + offset.rows) height [ok := tall]
  let columnBelow := Int.modNatLt (position.column.toInt + offset.columns) width [ok := wide]
  Both (omega [rowBelow]) (omega [columnBelow])

--| By zero, a position on the board stays put.
theorem wrapZero ∀ (position: Position) (height width: Nat)
    (inside: position.within height width = True):
    position.wrap Offset.zero height width = position :=
  positionExt
    (position.wrap Offset.zero height width)
    position
    (rewrite (omega: position.row.toInt + 0 = position.row.toInt) in
      Int.modNatOfLt height position.row (omega [inside.left]))
    (rewrite (omega: position.column.toInt + 0 = position.column.toInt) in
      Int.modNatOfLt width position.column (omega [inside.right]))

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
      (Eq.cong (x => Int.modNat x height) (omega)))
    (Eq.trans
      (Int.modNatModAdd (position.column.toInt + first.columns) second.columns width [ok := wide])
      (Eq.cong (x => Int.modNat x width) (omega)))

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
      Eq.sym
        (Eq.trans
          (Eq.cong
            (moved => position.wrap moved height width)
            (offsetExt (offset.times (Nat.toInt 0)) Offset.zero (omega) (omega)))
          (wrapZero position height width inside))
    | Succ times =>
      Eq.trans
        (wrapIterate offset height width times
          (position.wrap offset height width)
          (wrapWithin position offset height width))
        (Eq.trans
          (wrapPlus position offset (offset.times times.toInt) height width)
          (Eq.cong
            (moved => position.wrap moved height width)
            (offsetExt (offset.plus (offset.times times.toInt)) (offset.times (Succ times).toInt) (ring) (ring))))
