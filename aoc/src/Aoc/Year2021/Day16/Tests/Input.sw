-- The real puzzle input (aoc/inputs/2021/day16.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day16.Tests
import Aoc.Year2021.Day16 (..)
import Aoc.Year2021.Day16.Spec (versionTotal)
import Std (Fail)

def inputPacket: Packet := Fail.orElse (Literal 0 []) (() => parsePacket (include "../../../../../inputs/2021/day16.txt"))

test "real input, part 1" := solvePart1 inputPacket == 901
test "real input, part 2" := solvePart2 inputPacket == 110434737925
test "real input, part 1 by the spec" := versionTotal inputPacket == 901
