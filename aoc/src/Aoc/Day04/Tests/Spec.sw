-- Day 4's specification (Spec/Spec.sw) on the puzzle's example and small grids.

namespace Aoc.Day04.Tests
import Aoc.Day04 (..)
import Aoc.Day04.Spec (..)
import Std (Result, Vec)

def exampleGrid: Grid := Result.getOrElse (parseGrid example) ({ height = 0, width = 0, rows = VNil }: Grid)

def plusGrid: Grid := Result.getOrElse (parseGrid [".@.", "@@@", ".@."]) ({ height = 0, width = 0, rows = VNil }: Grid)

test "spec on the example" := part1Spec exampleGrid == 13
test "spec cells" := ((cellsOf exampleGrid) 0 2, (cellsOf exampleGrid) 0 0, (cellsOf exampleGrid) 10 2, neighbours exampleGrid (cellsOf exampleGrid) 0 2) == (Roll, Floor, Floor, 3)
test "adjacent" := adjacent 3 4 2 5 ∧ adjacent 0 0 1 1 ∧ not (adjacent 3 4 3 4) ∧ not (adjacent 3 4 5 4)
test "part 2 spec on a plus" := (part1Spec plusGrid, rollCount plusGrid (rounds plusGrid 1 (cellsOf plusGrid)), part2Spec plusGrid) == (4, 1, 5)
