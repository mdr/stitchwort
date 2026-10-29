-- The spec run as the program: part 1 is `totalDistance` of the sorted
-- lists, part 2 is `similarityScore`, which counts the right list once per
-- left id (quadratic) instead of building a count map.
namespace Scratch.Spec
import Aoc.Year2024.Day01 (parseLocationLists)
import Aoc.Year2024.Day01.Spec (similarityScore, totalDistance)
import Std (Fail, IO)

def main(): {IO, Fail} () :=
  let lists := parseLocationLists IO.readAll()
  IO.print "Part 1: ${totalDistance lists.left.sort lists.right.sort}"
  IO.print "Part 2: ${similarityScore lists}"
