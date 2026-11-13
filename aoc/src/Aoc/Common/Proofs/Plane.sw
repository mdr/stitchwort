--| Facts about the plane (Plane.sw): turning is four-periodic and undone by
--| the other turn, on headings and on coordinates, in every frame (the
--| frame's law `up * up = 1` is all they need); turning a heading turns
--| its step (`coordsTurnRightHeading`); stepping along a heading and back
--| returns (`coordsStepOpposite`); the Manhattan length is kept by a turn
--| and obeys the triangle inequality; coordinates add as numbers do; and
--| sheets, grid offsets and boxes convert without loss.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (And, Bool, Eq, Int, Nat, Option, Or, Void)

-- Iterating a step that has a period

--| Iterating a function that comes back to where it started after `period`
--| steps, a whole number of times over, comes back too.
theorem iterateCycles (f: a → a) (period: Nat) (cycle: ∀ (x: a) => Nat.iterate period f x = x) (times: Nat) (x: a): Nat.iterate (times * period) f x = x :=
  match times with
    | Zero => rfl
    | Succ times => rewrite Nat.iterateAdd f period (times * period) x, cycle x in iterateCycles f period cycle times x

--| So only the remainder of the count by the period counts.
theorem iterateMod (f: a → a) (period: Nat) [auto positive: period ≠ 0] (cycle: ∀ (x: a) => Nat.iterate period f x = x) (count: Nat) (x: a):
    Nat.iterate count f x = Nat.iterate (count % period) f x :=
  calc Nat.iterate count f x
    _ = Nat.iterate ((count / period) * period + count % period) f x := rewrite <- Nat.divModEq count period in rfl
    _ = Nat.iterate (count % period) f (Nat.iterate ((count / period) * period) f x) := Nat.iterateAdd f ((count / period) * period) (count % period) x
    _ = Nat.iterate (count % period) f x := rewrite iterateCycles f period cycle (count / period) x in rfl

-- Headings

theorem headingTurnRightFour (heading: Heading): heading.turnRight.turnRight.turnRight.turnRight = heading := cases

theorem headingTurnLeftRight (heading: Heading): heading.turnRight.turnLeft = heading := cases

theorem headingTurnRightLeft (heading: Heading): heading.turnLeft.turnRight = heading := cases

theorem headingOppositeTwoTurns (heading: Heading): heading.turnRight.turnRight = heading.opposite := cases

theorem headingOppositeOpposite (heading: Heading): heading.opposite.opposite = heading := cases

--| Four quarter turns are a full turn, so a count of quarter turns only matters modulo 4.
theorem headingTurnedMod (heading: Heading) (quarters: Nat): heading.turned quarters = heading.turned (quarters % 4) :=
  iterateMod Heading.turnRight 4 headingTurnedFour quarters heading

theorem headingTurnedFour (heading: Heading): Nat.iterate 4 Heading.turnRight heading = heading := headingTurnRightFour heading

theorem memHeadings (heading: Heading): heading ∈ headings := match heading with
  | North => Inl rfl
  | East => Inr (Inl rfl)
  | South => Inr (Inr (Inl rfl))
  | West => Inr (Inr (Inr (Inl rfl)))

theorem headingToDirectionToHeading (heading: Heading): heading.toDirection.toHeading = heading := cases

theorem directionToHeadingToDirection (direction: Direction): direction.toHeading.toDirection = direction := cases

--| Turning a heading is turning its direction on the grid, and likewise the other turns.
theorem headingToDirectionTurnRight (heading: Heading): heading.turnRight.toDirection = heading.toDirection.turnRight := cases

theorem headingToDirectionTurnLeft (heading: Heading): heading.turnLeft.toDirection = heading.toDirection.turnLeft := cases

theorem headingToDirectionOpposite (heading: Heading): heading.opposite.toDirection = heading.toDirection.opposite := cases

-- Coordinates

theorem coordsExt (coords other: Coords f) (sameX: coords.x = other.x) (sameY: coords.y = other.y): coords = other :=
  match coords, other with
    | { x, y }, { x = otherX, y = otherY } => rewrite sameX, sameY in rfl

theorem coordsPlusComm (coords: Coords f) (other: Coords f): coords.plus other = other.plus coords := coordsExt _ _ (omega) (omega)

theorem coordsPlusAssoc (coords: Coords f) (other: Coords f) (third: Coords f): (coords.plus other).plus third = coords.plus (other.plus third) :=
  coordsExt _ _ (omega) (omega)

theorem coordsPlusZero (coords: Coords f): coords.plus Coords.zero = coords := coordsExt _ _ (omega) (omega)

theorem coordsZeroPlus (coords: Coords f): Coords.zero.plus coords = coords := coordsExt _ _ (omega) (omega)

--| From `other`, the step to `coords` arrives at `coords`.
theorem coordsPlusMinus (coords: Coords f) (other: Coords f): other.plus (coords.minus other) = coords := coordsExt _ _ (omega) (omega)

theorem coordsMinusPlus (coords: Coords f) (other: Coords f): (coords.plus other).minus other = coords := coordsExt _ _ (omega) (omega)

theorem coordsNegatePlus (coords: Coords f): coords.plus coords.negate = Coords.zero := coordsExt _ _ (omega) (omega)

theorem coordsTimesPlus (coords: Coords f) (other: Coords f) (factor: Int): (coords.plus other).times factor = (coords.times factor).plus (other.times factor) :=
  coordsExt _ _ (ring) (ring)

-- Turning coordinates

theorem coordsTurnRightFour [auto frame: Frame f] (coords: Coords f): coords.turnRight.turnRight.turnRight.turnRight = coords :=
  coordsExt coords.turnRight.turnRight.turnRight.turnRight coords (ring [(frame.up * frame.up + 1) * coords.x * frame.unit])
    (ring [(frame.up * frame.up + 1) * coords.y * frame.unit])

theorem coordsTurnLeftRight [auto frame: Frame f] (coords: Coords f): coords.turnRight.turnLeft = coords :=
  coordsExt coords.turnRight.turnLeft coords (ring [coords.x * frame.unit]) (ring [coords.y * frame.unit])

theorem coordsTurnRightLeft [auto frame: Frame f] (coords: Coords f): coords.turnLeft.turnRight = coords :=
  coordsExt coords.turnLeft.turnRight coords (ring [coords.x * frame.unit]) (ring [coords.y * frame.unit])

theorem coordsTurnedFour [auto frame: Frame f] (coords: Coords f): Nat.iterate 4 Coords.turnRight coords = coords := coordsTurnRightFour coords

--| Only the remainder of the quarter turns by 4 counts.
theorem coordsTurnedMod [auto frame: Frame f] (coords: Coords f) (quarters: Nat): coords.turned quarters = coords.turned (quarters % 4) :=
  iterateMod Coords.turnRight 4 coordsTurnedFour quarters coords

--| Turning twice is negating.
theorem coordsTurnRightTwice [auto frame: Frame f] (coords: Coords f): coords.turnRight.turnRight = coords.negate :=
  coordsExt coords.turnRight.turnRight coords.negate (ring [coords.x * frame.unit]) (ring [coords.y * frame.unit])

--| The step along a turned heading is the turned step: turning a heading turns where it points.
theorem coordsTurnRightHeading [auto frame: Frame f] (heading: Heading): (heading.toCoords: Coords f).turnRight = heading.turnRight.toCoords :=
  match heading with
    | North => coordsExt _ _ (ring [frame.unit]) (ring)
    | East => coordsExt _ _ (omega) (omega)
    | South => coordsExt _ _ (ring [-frame.unit]) (ring)
    | West => coordsExt _ _ (omega) (omega)

theorem coordsTurnLeftHeading [auto frame: Frame f] (heading: Heading): (heading.toCoords: Coords f).turnLeft = heading.turnLeft.toCoords :=
  match heading with
    | North => coordsExt _ _ (ring [frame.unit]) (ring)
    | East => coordsExt _ _ (omega) (omega)
    | South => coordsExt _ _ (ring [frame.unit]) (ring)
    | West => coordsExt _ _ (omega) (omega)

theorem coordsTurnedHeading [auto frame: Frame f] (heading: Heading) (quarters: Nat): (heading.toCoords: Coords f).turned quarters = (heading.turned quarters).toCoords :=
  match quarters with
    | Zero => rfl
    | Succ quarters => calc (heading.toCoords: Coords f).turned (Succ quarters)
      _ = ((heading.toCoords: Coords f).turned quarters).turnRight := Nat.iterateSuccLast (Coords.turnRight: Coords f → Coords f) quarters heading.toCoords
      _ = (heading.turned quarters).toCoords.turnRight := rewrite coordsTurnedHeading heading quarters in rfl
      _ = (heading.turned quarters).turnRight.toCoords := coordsTurnRightHeading (heading.turned quarters)
      _ = (heading.turned (Succ quarters)).toCoords := rewrite Nat.iterateSuccLast Heading.turnRight quarters heading in rfl

-- Steps

--| The step the opposite way is the opposite step.
theorem headingOppositeCoords [auto frame: Frame f] (heading: Heading): (heading.opposite.toCoords: Coords f) = heading.toCoords.negate :=
  match heading with
    | North => coordsExt _ _ (omega) (omega)
    | East => coordsExt _ _ (omega) (omega)
    | South => coordsExt _ _ (omega) (omega)
    | West => coordsExt _ _ (omega) (omega)

--| A step along a heading then a step along the opposite one returns.
theorem coordsStepOpposite [auto frame: Frame f] (coords: Coords f) (heading: Heading): (coords.step heading).step heading.opposite = coords :=
  coordsExt _ _ (match heading with | North => omega | East => omega | South => omega | West => omega)
    (match heading with | North => omega | East => omega | South => omega | West => omega)

theorem coordsMovedZero [auto frame: Frame f] (coords: Coords f) (heading: Heading): coords.moved heading 0 = coords := coordsExt _ _ (omega) (omega)

--| Moving `distance + 1` is moving `distance` and then one more step.
theorem coordsMovedSucc [auto frame: Frame f] (coords: Coords f) (heading: Heading) (distance: Nat):
    coords.moved heading (distance + 1) = (coords.moved heading distance).step heading :=
  coordsExt _ _ (ring) (ring)

-- Distances

theorem manhattanZero: (Coords.zero: Coords f).manhattan = 0 := rfl

--| Only the origin has length 0.
theorem manhattanZeroOnly (coords: Coords f) (zero: coords.manhattan = 0): coords = Coords.zero :=
  coordsExt _ _ (Int.natAbsZero coords.x (omega)) (Int.natAbsZero coords.y (omega))

theorem manhattanNegate (coords: Coords f): coords.negate.manhattan = coords.manhattan :=
  rewrite Int.natAbsNegate coords.x, Int.natAbsNegate coords.y in rfl

theorem manhattanTimes (coords: Coords f) (factor: Int): (coords.times factor).manhattan = coords.manhattan * factor.natAbs :=
  rewrite Int.natAbsMul coords.x factor, Int.natAbsMul coords.y factor in ring

--| A frame's `up` is 1 or -1, so it keeps lengths.
theorem upAbs [auto frame: Frame f]: frame.up.natAbs = 1 := Int.natAbsOfMulSelfOne frame.up frame.unit

--| A quarter turn keeps the length, in every frame.
theorem manhattanTurnRight [auto frame: Frame f] (coords: Coords f): coords.turnRight.manhattan = coords.manhattan :=
  rewrite Int.natAbsNegate (frame.up * coords.x), Int.natAbsMul frame.up coords.y, Int.natAbsMul frame.up coords.x, upAbs [frame := frame] in
    omega

theorem manhattanTriangle (coords: Coords f) (other: Coords f): (coords.plus other).manhattan ≤ coords.manhattan + other.manhattan :=
  omega [Int.natAbsAdd coords.x other.x, Int.natAbsAdd coords.y other.y]

theorem distanceSelf (coords: Coords f): coords.distance coords = 0 :=
  let sameX: coords.x - coords.x = 0 := omega
  let sameY: coords.y - coords.y = 0 := omega
  rewrite sameX, sameY in rfl

theorem distanceSymm (coords: Coords f) (other: Coords f): coords.distance other = other.distance coords :=
  rewrite Int.natAbsSubComm coords.x other.x, Int.natAbsSubComm coords.y other.y in rfl

theorem distanceTriangle (coords: Coords f) (other: Coords f) (third: Coords f): coords.distance third ≤ coords.distance other + other.distance third :=
  let xs: (Coords.minus coords third).x.natAbs ≤ (Coords.minus coords other).x.natAbs + (Coords.minus other third).x.natAbs := Int.natAbsTriangle coords.x other.x third.x
  let ys: (Coords.minus coords third).y.natAbs ≤ (Coords.minus coords other).y.natAbs + (Coords.minus other third).y.natAbs := Int.natAbsTriangle coords.y other.y third.y
  omega

--| Only a place itself is at distance 0 from it.
theorem distanceZeroOnly (coords: Coords f) (other: Coords f) (zero: coords.distance other = 0): coords = other :=
  coordsExt _ _ (omega [Int.natAbsZero (coords.x - other.x) (omega)]) (omega [Int.natAbsZero (coords.y - other.y) (omega)])

-- Between the worlds

theorem pointToCoordsToPoint (point: Point): point.toCoords.toPoint = Some point := match point with
  | { x, y } => rfl

--| Coordinates that convert to a point are that point's.
theorem toPointSome (coords: Coords YDown) (point: Point) (converts: coords.toPoint = Some point): point.toCoords = coords :=
  match xAt: coords.x.toNatChecked with
    | Some x =>
      match yAt: coords.y.toNatChecked with
        | Some y =>
          rewrite <- Option.someInjective converts in
            coordsExt _ _ (Eq.sym (Int.toNatCheckedSome coords.x x xAt)) (Eq.sym (Int.toNatCheckedSome coords.y y yAt))

--| Negative coordinates are not a point.
theorem toPointNone (coords: Coords YDown) (negative: coords.x < 0 ∨ coords.y < 0): coords.toPoint = None := cases

theorem offsetToCoordsToOffset (offset: Offset): offset.toCoords.toOffset = offset := match offset with
  | { rows, columns } => rfl

theorem coordsToOffsetToCoords (coords: Coords YDown): coords.toOffset.toCoords = coords := match coords with
  | { x, y } => rfl

--| A point converted to coordinates and read as a grid offset is its position's offset from the corner.
theorem pointToCoordsOffset (point: Point): point.toCoords.toOffset = (point.toPosition.minus { row = 0, column = 0 }) := rfl

--| With `y` down, a heading's step is its grid direction's step.
theorem headingCoordsDown (heading: Heading): (heading.toCoords: Coords YDown) = heading.toDirection.offset.toCoords := cases

--| Turning on the page is the same turn on the grid: `YDown` coordinates turned right are the grid offset turned right.
theorem coordsTurnRightDown (heading: Heading): (heading.toCoords: Coords YDown).turnRight = heading.turnRight.toDirection.offset.toCoords :=
  rewrite coordsTurnRightHeading [f := YDown] heading in headingCoordsDown heading.turnRight

-- Boxes

--| `contains` as the inequalities it checks.
theorem boxContains (box: Box f) (coords: Coords f):
    box.contains coords = True ↔ box.low.x ≤ coords.x ∧ coords.x ≤ box.high.x ∧ box.low.y ≤ coords.y ∧ coords.y ≤ box.high.y :=
  { forward = holds => omega, backward = holds => omega }

--| A box contains its corners when it isn't empty.
theorem boxContainsLow (box: Box f) (nonempty: box.low.x ≤ box.high.x ∧ box.low.y ≤ box.high.y): box.contains box.low = True := omega

theorem boxContainsHigh (box: Box f) (nonempty: box.low.x ≤ box.high.x ∧ box.low.y ≤ box.high.y): box.contains box.high = True := omega

--| With `y` up the top is the largest `y`...
theorem boxTopYUp (box: Box YUp): box.top = box.high.y := rfl

theorem boxBottomYUp (box: Box YUp): box.bottom = box.low.y := rfl

--| ...and with `y` down the smallest.
theorem boxTopYDown (box: Box YDown): box.top = box.low.y := rfl

theorem boxBottomYDown (box: Box YDown): box.bottom = box.high.y := rfl

-- Sizes

theorem sizeContains (size: Size) (position: Position): size.contains position = True ↔ position.row < size.height ∧ position.column < size.width :=
  { forward = holds => omega, backward = holds => omega }
