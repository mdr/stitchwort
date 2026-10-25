-- Day 1's specification (Spec/Spec.sw) on the puzzle's example.

namespace Aoc.Day01.Tests
import Aoc.Day01 (..)
import Aoc.Day01.Spec (..)
import Std (Fail)

test "example, click by click" := zerosPassedSpec (Fail.orElse [] (() => parseTurns example)) startingDial == 6
