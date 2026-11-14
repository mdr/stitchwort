--| The program's steps are the spec's: `uphill` gives exactly the positions
--| on the map one step away (up, down, left or right) and one higher
--| (`memUphill`), each once, and `positions` lists every position with a
--| height, each once. The neighbours are the adjacent positions, each once,
--| by the shared grid code's `neighbourAdjacent`, `adjacentNeighbour` and
--| `neighboursDistinct`.

namespace Aoc.Year2024.Day10.Proofs
import Aoc.Year2024.Day10 (..)
import Aoc.Year2024.Day10.Spec (..)
import Aoc.Common (Position, cellAt, cells, memCellsOfCellAt)
import Aoc.Common.Proofs (adjacentNeighbour, cellPositionsDistinct, neighbourAdjacent, neighboursDistinct)
import Std (And, Bool, DecEq, Eq, Iff, List, Nat, Option, Void)

--| Every position with a height is on the list.
theorem positionsComplete ∀ (map: TopographicMap) (position: Position) (height: Nat)
    (has: map.heightAt position = Some height):
    position ∈ map.positions :=
  match found: cellAt map.grid.rows position with
    | Some tile =>
      List.memMap (cells map.grid.rows) (position, tile) (memCellsOfCellAt map.grid.rows position tile found) Pair.fst

--| Each position is on the list once.
theorem positionsDistinct ∀ (map: TopographicMap): List.Distinct map.positions := cellPositionsDistinct map.grid.rows

--| A position one higher than another has a height, so it is on the map.
theorem higherOnMap ∀ (map: TopographicMap) (from to: Position)
    (higher: increasesByOne map from to = True):
    to ∈ map.positions :=
  match known: map.heightAt from with | Some height => positionsComplete map to (height + 1) higher.read

--| `uphill` is the spec's steps from `from`.
theorem memUphill ∀ (map: TopographicMap) (from to: Position):
    to ∈ map.uphill from ↔ (to ∈ map.positions) ∧ (isStep map from to = True) :=
  {
    forward = member =>
      let both := List.memFilter from.neighbours (map.isOneHigher from) member
      Both
        (higherOnMap map from to (And.right both))
        (Both (neighbourAdjacent from to (And.left both)) (And.right both)),
    backward = has =>
      let Both adjacentStep higher := And.right has
      List.memFilterIntro from.neighbours (map.isOneHigher from) (adjacentNeighbour from to adjacentStep) higher
  }

theorem uphillDistinct ∀ (map: TopographicMap) (from: Position): List.Distinct (map.uphill from) :=
  List.distinctFilter from.neighbours (map.isOneHigher from) (neighboursDistinct from)

--| `uphill` is the spec's steps from `from` among the positions, in another
--| order.
theorem uphillPerm ∀ (map: TopographicMap) (from: Position):
    List.Perm (map.positions.filter (isStep map from)) (map.uphill from) :=
  List.permOfSameMembers
    (map.positions.filter (isStep map from))
    (map.uphill from)
    (List.distinctFilter map.positions (isStep map from) (positionsDistinct map))
    (uphillDistinct map from)
    (to member => (memUphill map from to).backward (List.memFilter map.positions (isStep map from) member))
    (to member =>
      let both := (memUphill map from to).forward member
      List.memFilterIntro map.positions (isStep map from) (And.left both) (And.right both))
