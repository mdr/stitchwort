--| Day 9's specification (Spec/Spec.sw) on the puzzle's example and small
--| cases: the spec's own reading, tile by tile, gives the puzzle's answers.

namespace Aoc.Year2025.Day09.Tests
import Aoc.Common (Line, Point)
import Aoc.Year2025.Day09 (..)
import Aoc.Year2025.Day09.Spec (..)
import Std (List, Nat, Result)

--| The largest area the spec allows, worked out tile by tile (slow: only
--| for small floors).
def specPart2 (tiles: List Point): Nat := rectangles tiles |> .filter (allRedOrGreen tiles) |> .map .area |> largest

test "the spec's rectangles" :=
  rectangles [tile 1 1, tile 2 2, tile 3 3]
    == [rectangle (tile 1 1) (tile 2 2), rectangle (tile 1 1) (tile 3 3), rectangle (tile 2 2) (tile 3 3)]
test "the spec's connections" :=
  connections [tile 1 1, tile 6 1, tile 6 4]
    == [line (tile 1 1) (tile 6 1), line (tile 6 1) (tile 6 4), line (tile 6 4) (tile 1 1)]
test "the spec on the example" := example.map specPart2 == Ok 24
test "the spec on a U" := specPart2 letterU == 32
test "the spec on a slot" := specPart2 slot == 36
test "red or green by the spec" :=
  example.map (tiles =>
    redOrGreen tiles (tile 7 1)
      ∧ redOrGreen tiles (tile 9 2)
      ∧ redOrGreen tiles (tile 3 4)
      ∧ ¬(redOrGreen tiles (tile 3 2))
      ∧ ¬(redOrGreen tiles (tile 12 4))
      ∧ ¬(redOrGreen tiles (tile 8 6)))
    == Ok True
