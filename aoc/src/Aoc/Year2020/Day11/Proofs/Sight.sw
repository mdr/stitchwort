--| Part 2's count is the spec's: walking out in a direction a step at a
--| time, past floor, finds the first seat of the spec's line of sight, so
--| the occupied seats the program counts over the eight directions are
--| the spec's occupied seats seen. That makes part 2's round the spec's on
--| any layout whose height and width the rule's reach is.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Aoc.Common (Grid, Offset, Position)
import Aoc.Common.Proofs (lookupAt, mapWidth)
import Std (Eq, List, Nat, Option)

--| Counting the values of a `filterMap` counts the elements whose value
--| passes.
theorem countFilterMap (f: a → Option b) (p: b → Bool): (xs: List a) → (xs.filterMap f).count p = xs.count (x => (f x).any p)
  | [] => rfl
  | [x, ..rest] =>
    rewrite List.countCons rest x (x => (f x).any p) in
    match f x with
      | None => rewrite countFilterMap f p rest in rfl
      | Some y => rewrite List.countCons (rest.filterMap f) y p, countFilterMap f p rest in rfl

--| The walk depends only on what `find` says at each position.
theorem firstSeatCong (f: Position → Option Seat) (g: Position → Option Seat) (same: (position: Position) → f position = g position)
    (from: Position) (direction: Offset): (distance: Nat) → (steps: Nat) → firstSeat f from direction distance steps = firstSeat g from direction distance steps
  | distance, Zero => rfl
  | distance, Succ more =>
    match from.offset (direction.times distance.toInt) with
      | None => rfl
      | Some next =>
        rewrite same next in
        match g next with
          | None => rfl
          | Some Floor => firstSeatCong f g same from direction (distance + 1) more
          | Some Empty => rfl
          | Some Occupied => rfl

--| The cell `distance` steps from `from` in `direction`, by what `find`
--| says is there (`Spec.cellAlong` with the layout's `at`).
def cellBy (find: Position → Option Seat) (from: Position) (direction: Offset) (distance: Nat): Option (Position, Seat) :=
  from.offset (direction.times distance.toInt) |> .flatMap (there => find there |> .map (seat => (there, seat)))

--| The cells `distance`, `distance + 1`, … steps away, `steps` of them, up
--| to the edge.
def sightFrom (find: Position → Option Seat) (from: Position) (direction: Offset) (distance: Nat) (steps: Nat): List (Position, Seat) :=
  List.rangeFrom steps distance |> .map (cellBy find from direction) |> .takeWhile (.isSome) |> .somes

--| Whether the walk ends at an occupied seat is whether the first seat on
--| the line of sight is occupied.
theorem walkSeen (find: Position → Option Seat) (from: Position) (direction: Offset): (distance: Nat) → (steps: Nat) →
    (firstSeat find from direction distance steps).any (near => find near == Some Occupied)
      = ((sightFrom find from direction distance steps).find (((_, seat)) => seat != Floor)).any (((_, seat)) => seat == Occupied)
  | distance, Zero => rfl
  | distance, Succ more =>
    match from.offset (direction.times distance.toInt) with
      | None => rfl
      | Some next =>
        match e: find next with
          | None => rfl
          | Some Floor => walkSeen find from direction (distance + 1) more
          | Some Empty => rewrite e in rfl
          | Some Occupied => rewrite e in rfl

--| Checking a position found for an occupied seat, with the table or
--| with `at`.
theorem anyLookup (layout: Layout) (found: Option Position):
    found.any (near => layout.grid.lookup near == Some Occupied) = found.any (near => layout.grid.at near == Some Occupied) :=
  match found with
    | None => rfl
    | Some near => rewrite lookupAt layout.grid near in rfl

--| In one direction, the program's walk with the table and the spec's
--| first seen seat agree on whether it is occupied, for a reach of the
--| layout's height plus its width.
theorem seenOccupied (layout: Layout) (from: Position) (direction: Offset) (reach: Nat) (fits: reach = layout.grid.height + layout.grid.width):
    (firstSeat layout.grid.lookup from direction 1 reach).any (near => layout.grid.lookup near == Some Occupied)
      = (Spec.firstSeen layout from direction).any (((_, seat)) => seat == Occupied) :=
  calc (firstSeat layout.grid.lookup from direction 1 reach).any (near => layout.grid.lookup near == Some Occupied)
    _ = (firstSeat layout.grid.at from direction 1 reach).any (near => layout.grid.lookup near == Some Occupied) :=
      rewrite firstSeatCong layout.grid.lookup layout.grid.at (position => lookupAt layout.grid position) from direction 1 reach in rfl
    _ = (firstSeat layout.grid.at from direction 1 reach).any (near => layout.grid.at near == Some Occupied) := anyLookup layout (firstSeat layout.grid.at from direction 1 reach)
    _ = ((sightFrom layout.grid.at from direction 1 reach).find (((_, seat)) => seat != Floor)).any (((_, seat)) => seat == Occupied) :=
      walkSeen layout.grid.at from direction 1 reach
    _ = (Spec.firstSeen layout from direction).any (((_, seat)) => seat == Occupied) := rewrite fits in rfl

--| The eight directions the program walks are the spec's.
theorem compassDirections: compass = Spec.directions := rfl

--| Part 2's count is the spec's occupied seats seen, for a reach of the
--| layout's height plus its width.
theorem sightOccupied (layout: Layout) (reach: Nat) (fits: reach = layout.grid.height + layout.grid.width) (position: Position):
    (compass.filterMap (direction => firstSeat layout.grid.lookup position direction 1 reach)).count (near => layout.grid.lookup near == Some Occupied)
      = Spec.occupiedSeen layout position :=
  rewrite countFilterMap (direction => firstSeat layout.grid.lookup position direction 1 reach) (near => layout.grid.lookup near == Some Occupied) compass,
    List.countCongMem compass (direction => (firstSeat layout.grid.lookup position direction 1 reach).any (near => layout.grid.lookup near == Some Occupied))
      (direction => (Spec.firstSeen layout position direction).any (((_, seat)) => seat == Occupied))
      (direction member => seenOccupied layout position direction reach fits) in rfl

--| Part 2's round, with the reach of a layout of the same height and
--| width, is the spec's.
theorem sightRound (start: Layout) (layout: Layout) (sameShape: start.grid.height + start.grid.width = layout.grid.height + layout.grid.width):
    layout.round start.sightRule = Spec.sightRound layout :=
  roundSpec layout start.sightRule (Spec.occupiedSeen layout) (position => sightOccupied layout (start.grid.height + start.grid.width) sameShape position)

--| A spec round keeps the layout's height and width.
theorem roundShape (layout: Layout) (considered: Position → Nat) (crowded: Nat):
    (Spec.round layout considered crowded).grid.height + (Spec.round layout considered crowded).grid.width = layout.grid.height + layout.grid.width :=
  let (Both wide tall) := mapWidth layout.grid (at seat => Spec.becomes seat (considered at) crowded)
  rewrite wide, tall in rfl
