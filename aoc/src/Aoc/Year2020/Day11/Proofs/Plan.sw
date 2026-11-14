--| Working the seats in view out once is sound: rounds never turn floor
--| into a seat or a seat into floor (`roundPlan`), so on every layout the
--| rounds reach, a seat's planned view, the seats the rule looks at on the
--| start, counts the same occupied seats as the rule looking at the layout
--| itself (`planCount`). Leaving out floor and positions off the layout
--| loses no occupied seat.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Aoc.Common (Grid, Position, cellAt)
import Aoc.Common.Proofs (cellAtMapCells, lookupAt, lookupOrAt)
import Std (Bool, Eq, Exists, List, Option, Void)

--| The same floor plan: the same positions on the layout, with floor at
--| the same ones.
def SamePlan (start layout: Layout): Prop :=
  ∀ (position: Position) => (cellAt layout.grid.rows position).map Seat.isSeat
    = (cellAt start.grid.rows position).map Seat.isSeat

theorem becomesIsSeat ∀ (seat: Seat) (occupiedNear crowded: Nat):
    (Spec.becomes seat occupiedNear crowded).isSeat = seat.isSeat :=
  cases

theorem mapKeepsSeat ∀ (found: Option Seat) (f: Seat → Seat)
    (keeps: ∀ (seat: Seat) => (f seat).isSeat = seat.isSeat):
    (found.map f).map Seat.isSeat = found.map Seat.isSeat :=
  match found with
    | None => rfl
    | Some seat => rewrite keeps seat in rfl

--| A spec round keeps the floor plan.
theorem roundPlan ∀ (start layout: Layout) (considered: Position → Nat) (crowded: Nat)
    (same: SamePlan start layout):
    SamePlan start (Spec.round layout considered crowded) :=
  position =>
    rewrite cellAtMapCells layout.grid.rows (at seat => Spec.becomes seat (considered at) crowded) position in
      Eq.trans
        (mapKeepsSeat
          (cellAt layout.grid.rows position)
          (seat => Spec.becomes seat (considered position) crowded)
          (seat => becomesIsSeat seat (considered position) crowded))
        (same position)

--| Where the layout has a seat, so has the start.
theorem startSeat ∀ (start layout: Layout)
    (same: SamePlan start layout)
    (position: Position) (here: Seat)
    (found: cellAt layout.grid.rows position = Some here)
    (seat: here.isSeat = True):
    ∃ (before: Seat) => cellAt start.grid.rows position = Some before ∧ before.isSeat = True :=
  let plan := same position
  rewrite found at plan in
    match e: cellAt start.grid.rows position with
      | Some before => Witness before (Both rfl (rewrite <- Option.someInjective plan in seat))

--| An occupied seat on the layout is a seat on the start.
theorem occupiedSeat ∀ (start layout: Layout)
    (same: SamePlan start layout) (near: Position)
    (occupied: (layout.grid.lookup near == Some Occupied) = True):
    (start.grid.lookup near).any (.isSeat) = True :=
  rewrite lookupAt start.grid near in
    match e: cellAt layout.grid.rows near with
      | None => Void.exfalso (Bool.falseNotTrue (rewrite lookupAt layout.grid near, e at occupied in occupied))
      | Some here =>
        match here with
          | Occupied => Exists.elim (startSeat start layout same near Occupied e rfl) (before both =>
            rewrite And.left both in And.right both)
          | Empty => Void.exfalso (Bool.falseNotTrue (rewrite lookupAt layout.grid near, e at occupied in occupied))
          | Floor => Void.exfalso (Bool.falseNotTrue (rewrite lookupAt layout.grid near, e at occupied in occupied))

--| A seat's planned view is what the rule looks at on the start, seats
--| only.
theorem planInView ∀ (rule: Rule) (start layout: Layout)
    (same: SamePlan start layout)
    (position: Position) (here: Seat)
    (found: cellAt layout.grid.rows position = Some here)
    (seat: here.isSeat = True):
    (rule.planFor start).inView position
      = (rule.inView start.grid.lookup position).filter (near => (start.grid.lookup near).any (.isSeat)) :=
  Exists.elim (startSeat start layout same position here found seat) (before both =>
    let looks := (at: Position) (cell: Seat) =>
      if cell.isSeat then rule.inView start.grid.lookup at |> .filter (near => (start.grid.lookup near).any (.isSeat))
      else []
    rewrite lookupOrAt (start.grid.map looks) [] position,
        cellAtMapCells start.grid.rows looks position,
        And.left both,
        And.right both in
      rfl)

--| On a layout with the start's floor plan, a seat's planned view counts
--| the occupied seats the rule sees on the layout, when the rule looks at
--| the same positions on both.
theorem planCount ∀ (rule: Rule) (start layout: Layout)
    (same: SamePlan start layout)
    (position: Position) (here: Seat)
    (found: cellAt layout.grid.rows position = Some here)
    (seat: here.isSeat = True)
    (sameView: rule.inView start.grid.lookup position = rule.inView layout.grid.lookup position):
    ((rule.planFor start).inView position).count (near => layout.grid.lookup near == Some Occupied)
      = (rule.inView layout.grid.lookup position).count (near => layout.grid.lookup near == Some Occupied) :=
  rewrite planInView rule start layout same position here found seat,
      List.countFilter
        (rule.inView start.grid.lookup position)
        (near => layout.grid.lookup near == Some Occupied)
        (near => (start.grid.lookup near).any (.isSeat))
        (near occupied => occupiedSeat start layout same near occupied),
      sameView in
    rfl
