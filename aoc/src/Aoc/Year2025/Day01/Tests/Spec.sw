--| Day 1's specification (Spec/Spec.sw) on the puzzle's example.

namespace Aoc.Year2025.Day01.Tests
import Aoc.Year2025.Day01 (..)
import Aoc.Year2025.Day01.Spec (..)
import Std (Fail)

test "example, click by click" := exampleTurns.map (turns => zerosPassedSpec turns Dial.start) == Ok 6
