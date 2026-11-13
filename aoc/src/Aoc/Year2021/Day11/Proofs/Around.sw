--| Counting the flashers among the eight positions around an octopus counts
--| the spec's flashing neighbours. The eight around are exactly the
--| touching positions, without repeats, by the shared grid code
--| (`aroundTouching`, `touchingAround`, `aroundDistinct`).

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, touching)
import Aoc.Common.Proofs (aroundDistinct, aroundTouching, cellPositionsDistinct, touchingAround)
import Std (Bool, Eq, List, Nat)

--| Counting the flashers around `at` counts the spec's flashing
--| neighbours, when only octopuses on the grid flash.
theorem countAround (cavern: Cavern) (flashed: Position → Bool)
    (onGrid: ∀ (q: Position) => flashed q = True → q ∈ cavern.grid.cells.map Pair.fst) (at: Position):
    at.around.count flashed = flashingNeighbours cavern flashed at :=
  let positions := cavern.grid.cells.map Pair.fst
  let near := (q: Position) => touching at q && flashed q
  let same: List.Perm (at.around.filter flashed) (positions.filter near) :=
    List.permOfSameMembers (at.around.filter flashed) (positions.filter near) (List.distinctFilter at.around flashed (aroundDistinct at))
      (List.distinctFilter positions near (cellPositionsDistinct cavern.grid.rows))
      (q member =>
        let (Both inAround flashes) := List.memFilter at.around flashed member
        List.memFilterIntro positions near (onGrid q flashes) (Both (aroundTouching at q inAround) flashes))
      (q member =>
        let (Both inGrid both) := List.memFilter positions near member
        List.memFilterIntro at.around flashed (touchingAround at q (Bool.andLeft both)) (Bool.andRight both))
  calc at.around.count flashed
    _ = (at.around.filter flashed).length := Eq.sym (List.lengthFilter at.around flashed)
    _ = (positions.filter near).length := List.permLength _ _ same
    _ = positions.count near := List.lengthFilter positions near
    _ = flashingNeighbours cavern flashed at := List.countMap cavern.grid.cells near Pair.fst
