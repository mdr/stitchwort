-- The real puzzle input (aoc/inputs/2021/day13.txt, committed), through
-- `include`: the answers are checked on it when the tests run.
namespace Aoc.Year2021.Day13.Tests
import Aoc.Year2021.Day13 (..)
import Std (Fail, List)

def inputPaper: Paper := Fail.orElse { dots = [], folds = [] } (() => parsePaper (include "../../../../../inputs/2021/day13.txt"))

test "real input, part 1" := solvePart1 inputPaper == 666

-- The picture spells CJHAZHKU (Matt's Scala solution's picture, row for
-- row); `readLetters` reads it.
test "real input, part 2" :=
  showPicture (solvePart2 inputPaper)
    == ".##....##.#..#..##..####.#..#.#..#.#..#\n#..#....#.#..#.#..#....#.#..#.#.#..#..#\n#.......#.####.#..#...#..####.##...#..#\n#.......#.#..#.####..#...#..#.#.#..#..#\n#..#.#..#.#..#.#..#.#....#..#.#.#..#..#\n.##...##..#..#.#..#.####.#..#.#..#..##."
test "real input, part 2's letters" := readLetters (solvePart2 inputPaper) == "CJHAZHKU"
