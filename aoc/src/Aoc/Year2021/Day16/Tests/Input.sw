--| The real puzzle input (aoc/inputs/2021/day16.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day16.Tests
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (versionTotal)
import Std (Fail, Text)

def inputPacket: Result Packet Text :=
  Fail.toResult (() => parsePacket (include "../../../../../inputs/2021/day16.txt"))

test "real input, part 1" := inputPacket.map solvePart1 == Ok 901
test "real input, part 2" := inputPacket.map solvePart2 == Ok 110434737925
test "real input, part 1 by the spec" := inputPacket.map versionTotal == Ok 901
