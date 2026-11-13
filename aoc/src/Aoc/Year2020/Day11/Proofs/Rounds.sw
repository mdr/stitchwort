--| A round of the program is the spec's when each seat's count is: a seat
--| changes as the rules say (`roundSpec`), and part 1's count over the
--| eight positions around, looked up in the layout's table, is the spec's
--| count of adjacent occupied seats. Part 2's count is in Sight.sw.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Aoc.Common (Grid, Position, cellAt)
import Aoc.Common.Proofs (countAround, lookupAt, mapCellsCongAt)
import Std (Eq, List, Option)

theorem nextBecomes ∀ (seat: Seat) (occupiedNear: Nat) (crowded: Nat): seat.next occupiedNear crowded = Spec.becomes seat occupiedNear crowded := cases

--| Whether the table says a position holds an occupied seat.
theorem lookupOccupied ∀ (layout: Layout) (near: Position): (layout.grid.lookup near == Some Occupied) = (cellAt layout.grid.rows near).any (== Occupied) :=
  rewrite lookupAt layout.grid near in
  match cellAt layout.grid.rows near with
    | None => rfl
    | Some seat => cases

--| A round by a plan whose count of occupied seats in view from each seat
--| is `considered` is the spec's round with that count.
theorem roundSpec ∀ (layout: Layout) (plan: Plan) (considered: Position → Nat)
    (counts: ∀ (position: Position) (here: Seat) => cellAt layout.grid.rows position = Some here → here.isSeat = True →
      (plan.inView position).count (near => layout.grid.lookup near == Some Occupied) = considered position):
    layout.round plan = Spec.round layout considered plan.tolerance :=
  Layout.ext _ _ (Grid.ext _ _ (mapCellsCongAt layout.grid.rows
    (position here => here.next ((plan.inView position).count (near => layout.grid.lookup near == Some Occupied)) plan.tolerance)
    (position seat => Spec.becomes seat (considered position) plan.tolerance)
    (position here found =>
      match here with
        | Floor => rfl
        | Empty => rewrite counts position Empty found rfl in nextBecomes Empty (considered position) plan.tolerance
        | Occupied => rewrite counts position Occupied found rfl in nextBecomes Occupied (considered position) plan.tolerance)))

--| Part 1: the occupied seats among the eight positions around are the
--| occupied adjacent seats.
theorem aroundOccupied ∀ (layout: Layout) (position: Position):
    position.around.count (near => layout.grid.lookup near == Some Occupied) = Spec.occupiedAdjacent layout position :=
  rewrite List.countCongMem position.around (near => layout.grid.lookup near == Some Occupied) (near => (cellAt layout.grid.rows near).any (== Occupied))
    (near member => lookupOccupied layout near) in
  countAround layout.grid.rows (== Occupied) position
