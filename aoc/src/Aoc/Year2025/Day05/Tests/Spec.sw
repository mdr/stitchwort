--| Day 5's specification (Spec/Spec.sw) on the puzzle's example.

namespace Aoc.Year2025.Day05.Tests
import Aoc.Year2025.Day05 (..)
import Aoc.Year2025.Day05.Spec (..)
import Std (Result)

test "example brute force" := exampleDatabase.map countFresh == Ok 14
