-- Counting the flashers among the eight positions around an octopus counts
-- the spec's flashing neighbours. The eight around are exactly the
-- touching positions, without repeats, by the shared grid code
-- (`aroundTouching`, `touchingAround`, `aroundDistinct`).

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, cells, touching)
import Aoc.Common.Proofs (aroundDistinct, aroundTouching, cellPositionsDistinct, touchingAround)
import Std (Bool, Eq, List, Nat)

-- Counting the flashers around `at` counts the spec's flashing
-- neighbours, when only octopuses on the grid flash.
theorem countAround (levels: List (List Nat)) (flashed: Position → Bool)
    (onGrid: (q: Position) → flashed q = True → q ∈ (cells levels).map Pair.fst) (at: Position):
    at.around.count flashed = flashingNeighbours levels flashed at :=
  let positions := (cells levels).map Pair.fst
  let near := (q: Position) => touching at q && flashed q
  let same: List.Perm (at.around.filter flashed) (positions.filter near) :=
    List.permOfSameMembers (at.around.filter flashed) (positions.filter near) (List.distinctFilter at.around flashed (aroundDistinct at))
      (List.distinctFilter positions near (cellPositionsDistinct levels))
      (q member =>
        let (Both inAround flashes) := List.memFilter at.around flashed q member
        List.memFilterIntro positions near q (onGrid q flashes) (Bool.andIntro _ _ (aroundTouching at q inAround) flashes))
      (q member =>
        let (Both inGrid both) := List.memFilter positions near q member
        List.memFilterIntro at.around flashed q (touchingAround at q (Bool.andLeft _ _ both)) (Bool.andRight _ _ both))
  calc at.around.count flashed
    _ = (at.around.filter flashed).length := Eq.sym (List.lengthFilter at.around flashed)
    _ = (positions.filter near).length := List.permLength _ _ same
    _ = positions.count near := List.lengthFilter positions near
    _ = flashingNeighbours levels flashed at := List.countMap (cells levels) near Pair.fst
