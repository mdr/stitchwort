-- Day 19 proved: for every onsen whose patterns each have a stripe, part 1
-- counts the designs the puzzle calls possible (`part1Correct`) and part 2
-- adds up the puzzle's ways to make each design (`part2Correct`). Both
-- rest on `waysCorrect` (Table.sw): the program's table of suffix counts
-- follows the spec's count of towel lists (Counting.sw). The parser only
-- reads patterns with a stripe (`many1 stripe`); that isn't proved.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (..)
import Aoc.Year2024.Day19.Spec (..)
import Std (List, Nat)

-- A design is possible exactly when there are ways to make it.
theorem possibleWays (patterns: List Pattern) (design: Design): (ways patterns design > 0) = possible patterns design :=
  match arrangements patterns design with
    | Nil => rfl
    | Cons first rest => rfl

theorem part1Correct (onsen: Onsen) (striped: Striped onsen.patterns): solvePart1 onsen = part1 onsen :=
  List.countCongMem onsen.designs (design => waysToMake onsen.patterns design > 0) (possible onsen.patterns)
    (design member => rewrite waysCorrect onsen.patterns striped design in possibleWays onsen.patterns design)

theorem part2Correct (onsen: Onsen) (striped: Striped onsen.patterns): solvePart2 onsen = part2 onsen :=
  List.sumByCongMem onsen.designs (waysToMake onsen.patterns) (ways onsen.patterns) (design member => waysCorrect onsen.patterns striped design)
