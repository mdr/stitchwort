-- Day 6's specification (Spec/Spec.sw) on the puzzle's example.

namespace Aoc.Day06.Tests
import Aoc.Day06 (..)
import Aoc.Day06.Spec (..)
import Std (Option)

test "spec on the example" := (part1Spec example, part2Spec example) == (4277556, 3263827)
test "spec problem columns" := isProblem example 0 3 && isProblem example 12 15 && not (isProblem example 0 2) && not (isProblem example 1 3)
test "spec numbers" := (rowNumbers example 4 7, columnNumbers example 4 7, operatorOf example 4 7) == ([328, 64, 98], [8, 248, 369], Some Add)
