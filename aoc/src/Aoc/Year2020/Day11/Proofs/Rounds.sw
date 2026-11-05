--| A round of the program is the spec's: a seat changes as the rules say,
--| and part 1's count over the eight positions around (looked up in the
--| layout's table) is the spec's count of adjacent occupied seats.
--| Part 2's count is in Sight.sw.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Aoc.Common (Grid, Position, cellAt)
import Aoc.Common.Proofs (countAround, lookupAt, mapCellsCong)
import Std (Eq, List, Option)

theorem nextBecomes (seat: Seat) (occupiedNear: Nat) (crowded: Nat): seat.next occupiedNear crowded = Spec.becomes seat occupiedNear crowded := cases

--| Whether the table says a position holds an occupied seat.
theorem lookupOccupied (layout: Layout) (near: Position): (layout.grid.lookup near == Some Occupied) = (cellAt layout.grid.rows near).any (== Occupied) :=
  rewrite lookupAt layout.grid near in
  match cellAt layout.grid.rows near with
    | None => rfl
    | Some seat => cases

--| A round by a rule whose count of occupied seats in view is `considered`
--| is the spec's round with that count.
theorem roundSpec (layout: Layout) (rule: Rule) (considered: Position → Nat)
    (counts: (at: Position) → (rule.inView layout.grid.lookup at).count (near => layout.grid.lookup near == Some Occupied) = considered at):
    layout.round rule = Spec.round layout considered rule.tolerance :=
  Layout.ext _ _ (Grid.ext _ _ (mapCellsCong layout.grid.rows
    (at here => here.next ((rule.inView layout.grid.lookup at).count (near => layout.grid.lookup near == Some Occupied)) rule.tolerance)
    (at seat => Spec.becomes seat (considered at) rule.tolerance)
    (position here => rewrite counts position in nextBecomes here (considered position) rule.tolerance)))

--| Part 1: the occupied seats among the eight positions around are the
--| occupied adjacent seats.
theorem aroundOccupied (layout: Layout) (position: Position):
    position.around.count (near => layout.grid.lookup near == Some Occupied) = Spec.occupiedAdjacent layout position :=
  rewrite List.countCongMem position.around (near => layout.grid.lookup near == Some Occupied) (near => (cellAt layout.grid.rows near).any (== Occupied))
    (near member => lookupOccupied layout near) in
  countAround layout.grid.rows (== Occupied) position

--| Part 1's round is the spec's.
theorem adjacentRound (layout: Layout): layout.round adjacentRule = Spec.adjacentRound layout :=
  roundSpec layout adjacentRule (Spec.occupiedAdjacent layout) (position => aroundOccupied layout position)
