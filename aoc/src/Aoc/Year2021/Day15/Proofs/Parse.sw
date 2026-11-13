--| The parser keeps the puzzle's promise: what `parseCave` reads is a
--| rectangle of digits with at least one, the `Rectangle` the answers'
--| theorems assume (the shared grid parser's `parseGridRectangle`). So the
--| answers are the spec's for every input the parser accepts, with no
--| hypothesis (`part1FromInput`, `part2FromInput`). Levels are digits by
--| their type (`Fin 10`). The puzzle's levels are 1 to 9, but 0 needn't be
--| excluded: a 0 is a path step that costs nothing, and the tiling's wrap
--| is right for it too (`iterateRaise` needs only a level of at most 9).
-- (D2108)

namespace Aoc.Year2021.Day15.Proofs
import Aoc.Year2021.Day15 (..)
import Aoc.Year2021.Day15.Spec (..)
import Aoc.Common (parseGrid)
import Aoc.Common.Proofs (parseGridRectangle)
import Std (Eq, Fail, Fin, List, Nat, Result)
import Std.Parse (digit)

--| What `parseCave` reads is a rectangle with a digit.
theorem parseRectangle ∀ (input: Text) (cave: Cave) (parsed: Fail.toResult (() => parseCave input) = Ok cave): Rectangle cave :=
  let split := rewrite Fail.toResultThen (() => parseGrid input digit) (grid => ({ grid }: Cave)) at parsed
  Result.flatMapEqOk (Fail.toResult (() => parseGrid input digit)) (grid => Fail.toResult (() => ({ grid }: Cave))) cave split
    (grid read made =>
      let same: ({ grid }: Cave) = cave := Result.okInjective made
      let (Both rectangle (Both wide _)) := parseGridRectangle input digit grid read
      rewrite <- same in Both wide rectangle)

--| Part 1's answer is the lowest total risk, for every input the parser
--| accepts.
theorem part1FromInput ∀ (input: Text) (cave: Cave) (parsed: Fail.toResult (() => parseCave input) = Ok cave): Part1Answer cave (solvePart1 cave) :=
  part1Correct cave (parseRectangle input cave parsed)

--| Part 2's answer is the lowest total risk through the full cave, for
--| every input the parser accepts.
theorem part2FromInput ∀ (input: Text) (cave: Cave) (parsed: Fail.toResult (() => parseCave input) = Ok cave): Part2Answer cave (solvePart2 cave) :=
  part2Correct cave (parseRectangle input cave parsed)
