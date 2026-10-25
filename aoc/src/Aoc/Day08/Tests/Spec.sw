-- Day 8's specification (Spec/Spec.sw) on the puzzle's example and small cases.

namespace Aoc.Day08.Tests
import Aoc.Day08 (..)
import Aoc.Day08.Spec (..)
import Std (List, Result)

test "the example's first connections" :=
  example.map (boxes => firstConnections 4 boxes.points) == Ok [(0, 19), (0, 7), (2, 13), (7, 19)]
test "pairs at equal distances come in box order" :=
  connectionOrder [{ x = 0, y = 0, z = 0 }, { x = 1, y = 0, z = 0 }, { x = 2, y = 0, z = 0 }] == [(0, 1), (1, 2), (0, 2)]
