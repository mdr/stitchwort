-- Day 7's specification (Spec/Spec.sw) on the puzzle's example and small manifolds.

namespace Aoc.Year2025.Day07.Tests
import Aoc.Year2025.Day07 (..)
import Aoc.Year2025.Day07.Spec (..)
import Std (Option)

test "spec on the example" := (parseManifoldOption example).map (m => (part1Spec m, part2Spec m)) == Some (21, 40)
test "spec at the edges" :=
  ((parseManifoldOption ["S.", "^.", ".."]).map (m => (part1Spec m, part2Spec m)), (parseManifoldOption [".S", ".^", ".^"]).map (m => (part1Spec m, part2Spec m)))
    == (Some (1, 2), Some (1, 2))
test "spec timelines" :=
  (parseManifoldOption ["..S..", "..^..", ".^.^.", "..^.."]).map (m => timelines m |> .map (t => t.map (hit => (hit.row, hit.column, hit.turn == Left))))
    == Some [
      [(0, 2, True), (1, 1, True)],
      [(0, 2, True), (1, 1, False), (2, 2, True)],
      [(0, 2, True), (1, 1, False), (2, 2, False)],
      [(0, 2, False), (1, 3, True), (2, 2, True)],
      [(0, 2, False), (1, 3, True), (2, 2, False)],
      [(0, 2, False), (1, 3, False)]
    ]
