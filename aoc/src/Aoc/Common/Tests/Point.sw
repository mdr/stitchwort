--| Tests for points and lines.

namespace Aoc.Common.Tests
import Aoc.Common (..)
import Std (List)

def line (x1 y1 x2 y2: Nat): Line := { from = { x = x1, y = y1 }, to = { x = x2, y = y2 } }

test "a point is a position with x as the column" := ({ x = 3, y = 7 }: Point).toPosition == { row = 7, column = 3 }
test "points order by x, then y" :=
  Ord.compare ({ x = 1, y = 9 }: Point) { x = 2, y = 0 } == Less
    ∧ Ord.compare ({ x = 1, y = 2 }: Point) { x = 1, y = 3 } == Less
test "shapes" :=
  ((line 1 1 1 3).isVertical, (line 1 1 3 1).isHorizontal, (line 1 1 3 3).isDiagonal, (line 0 0 4 2).isDiagonal)
    == (True, True, True, False)
test "a line of one point is straight both ways" :=
  (line 4 4 4 4).isStraight ∧ (line 4 4 4 4).isVertical ∧ (line 4 4 4 4).isHorizontal
test "a vertical line's points" := (line 1 1 1 3).points == [{ x = 1, y = 1 }, { x = 1, y = 2 }, { x = 1, y = 3 }]
test "a diagonal line's points, either way" :=
  (line 9 7 7 9).points == [{ x = 9, y = 7 }, { x = 8, y = 8 }, { x = 7, y = 9 }]
