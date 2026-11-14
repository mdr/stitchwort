--| The real puzzle input (aoc/inputs/2021/day13.txt, committed), through
--| `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day13.Tests
import Aoc.Year2021.Day13 (..)
import Std (Fail, List, Text)

def inputPaper: Result Paper Text := Fail.toResult (() => parsePaper (include "../../../../../inputs/2021/day13.txt"))

test "real input, part 1" := inputPaper.map solvePart1 == Ok 666

--| The picture spells CJHAZHKU (Matt's Scala solution's picture, row for
--| row); `readLetters` reads it.
test "real input, part 2" :=
  inputPaper.map (paper => showPicture (solvePart2 paper))
    == Ok
      (".##....##.#..#..##..####.#..#.#..#.#..#\n#..#....#.#..#.#..#....#.#..#.#.#..#..#\n#.......#.####.#..#...#..####.##...#..#\n#.......#.#..#.####..#...#..#.#.#..#..#\n#..#.#..#.#..#.#..#.#....#..#.#.#..#..#\n.##...##..#..#.#..#.####.#..#.#..#..##.")
test "real input, part 2's letters" := inputPaper.map (paper => readLetters (solvePart2 paper)) == Ok "CJHAZHKU"
