-- Day 5's specification (Spec/Spec.sw) on the puzzle's example.

namespace Aoc.Year2025.Day05.Tests
import Aoc.Year2025.Day05 (..)
import Aoc.Year2025.Day05.Spec (..)
import Std (Fail)

test "example brute force" := countFresh (Fail.orElse emptyDatabase (() => parseDatabase example)) == 14
